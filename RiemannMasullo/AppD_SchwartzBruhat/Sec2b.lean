module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1d
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! # Schwartz–Bruhat isotypes and coarser topologies -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology UniformSpace
open scoped NNReal TensorProduct

section SchwartzBruhatAction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G] [hSC : SecondCountableTopology G]

include hSC in
/-- Paper: Proposition D.1.9.2, p. 781. The existing left translations
assemble into an action by continuous linear operators. -/
theorem existsUnique_schwartzBruhatTranslationAction :
    ∃! ρ : G →* (SchwartzBruhat G →L[ℂ] SchwartzBruhat G),
      ∀ g f, ρ g f = schwartzBruhatTranslate g f := by
  let T (g : G) : SchwartzBruhat G →L[ℂ] SchwartzBruhat G :=
    { toFun := schwartzBruhatTranslate g
      map_add' := fun f h ↦ Subtype.ext (funext fun x ↦ rfl)
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ rfl)
      cont := (schwartzBruhatTranslate_continuous (G := G)).comp
        (continuous_const.prodMk continuous_id) }
  let ρ : G →* (SchwartzBruhat G →L[ℂ] SchwartzBruhat G) :=
    { toFun := T
      map_one' := ContinuousLinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ by
        change f ((1 : G)⁻¹ * x) = f x
        rw [inv_one, one_mul])
      map_mul' := fun g h ↦ ContinuousLinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ by
        change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
        rw [mul_inv_rev, mul_assoc]) }
  refine ⟨ρ, fun _ _ ↦ rfl, ?_⟩
  intro τ hτ
  exact MonoidHom.ext fun g ↦ ContinuousLinearMap.ext (hτ g)

/-- Paper: (D.2.1.1), p. 792. Use the continuous linear representation
given by the left translations on the Schwartz–Bruhat space. -/
def schwartzBruhatTranslationAction : G →* (SchwartzBruhat G →L[ℂ] SchwartzBruhat G) :=
  Classical.choose (existsUnique_schwartzBruhatTranslationAction (G := G)).exists

/-- Paper: (D.2.1.2), p. 792. The bundled left translation is given
by evaluation at the inverse translate. -/
theorem schwartzBruhatTranslationAction_apply (g x : G) (f : SchwartzBruhat G) :
    schwartzBruhatTranslationAction (G := G) g f x = f (g⁻¹ * x) := by
  have h : schwartzBruhatTranslationAction (G := G) g f = schwartzBruhatTranslate g f :=
    (Classical.choose_spec (existsUnique_schwartzBruhatTranslationAction (G := G)).exists) g f
  rw [h]
  rfl

end SchwartzBruhatAction

section Projector

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
  (μ₁ : Measure m.toMonoidHom.ker) [hμ₁ : μ₁.IsHaarMeasure]

include hm hμ₁

local notation "K" => m.toMonoidHom.ker
local notation "S" => SchwartzBruhat G
local notation "ρS" => MonoidHom.comp (schwartzBruhatTranslationAction (G := G)) (Subgroup.subtype K)

omit hm hμ₁ [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- Point evaluation on the Schwartz–Bruhat space is continuous because its
absolute value pulls back to a continuous seminorm on every elementary stage. -/
private theorem continuous_schwartzBruhat_eval (x : G) : Continuous (fun f : S ↦ f x) := by
  classical
  let L : S →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hp : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    intro a e
    let q := (normSeminorm ℂ ℂ).comp (L.comp (schwartzBruhatStageInclusion a e))
    change Continuous q
    let p₀ : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hp₀ : Continuous p₀ :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (0, 0, 0, 0)
    apply Seminorm.continuous_of_le hp₀
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ p₀ f
    let := e.finiteGroup
    have he := schwartzBruhatStageRealization_apply a e f x
    by_cases hx : x ∈ a.val.1
    · rw [dite_eq_left hx] at he
      rw [he]
      let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      have hb : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) :=
        (le_iSup (fun g ↦ (‖f.val g‖₊ : ENNReal)) y).trans_eq
          (elementarySchwartzBound_zero f.val).symm
      exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
    · rw [dite_eq_right hx] at he
      exact ((congrArg norm he).trans (norm_zero (E := ℂ))).le.trans (apply_nonneg p₀ f)
  let i : {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion a e)} := ⟨p, hp⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

/-- Paper: (D.2.1.1), pp. 792–793. The normalized character average exists
as a continuous linear endomorphism of the Schwartz–Bruhat space. -/
theorem existsUnique_schwartzBruhatIsotypicProjector (ω : PontryaginDual K) :
    ∃! P : S →L[ℂ] S, ∀ (f : S) (x : G),
      P f x = (μ₁.real univ)⁻¹ •
        ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : ContinuousSMul ℂ S := (withGeneratingSeminorms_spec _ _).continuousSMul
  have : LocallyConvexSpace ℝ S := (withGeneratingSeminorms_spec _ _).toLocallyConvexSpace
  have : T2Space S := T2Space.of_injective_continuous
    (f := fun f : S ↦ (f : G → ℂ)) (fun _ _ h ↦ Subtype.ext h)
    (continuous_pi continuous_schwartzBruhat_eval)
  have : QuasiCompleteSpace ℂ S := schwartzBruhat_quasiComplete
  let τ : K →* (S →L[ℂ] S) := ρS
  have hρ (k : K) (f : S) : τ k f = schwartzBruhatTranslate (k : G) f :=
    (Classical.choose_spec (existsUnique_schwartzBruhatTranslationAction (G := G)).exists) k f
  have hτ : Continuous (fun p : K × S ↦ τ p.1 p.2) := by
    have hc : Continuous (fun p : K × S ↦ schwartzBruhatTranslate (p.1 : G) p.2) :=
      (schwartzBruhatTranslate_continuous (G := G)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    exact hc.congr fun p ↦ (hρ p.1 p.2).symm
  have hseq {E : Type _} [UniformSpace E] (T : K → E → E)
      (hT : Continuous (fun p : K × E ↦ T p.1 p.2))
      (u : ℕ → E) (v : E) (hu : Tendsto u atTop (𝓝 v)) :
      TendstoUniformly (fun n k ↦ T k (u n)) (fun k ↦ T k v) atTop := by
    intro U hU
    have hc : Continuous (fun p : E × K ↦ T p.2 p.1) := hT.comp continuous_swap
    obtain ⟨W, hW, h⟩ := (isCompact_univ (X := K)).mem_uniformity_of_prod
      (f := fun f : E ↦ fun k : K ↦ T k f)
      (s := univ) (q := v) hc.continuousOn (mem_univ v) (symm_le_uniformity hU)
    rw [nhdsWithin_univ] at hW
    filter_upwards [hu.eventually hW] with n hn k
    exact h (u n) hn k (mem_univ k)
  have hex : ∃ A : S →L[ℂ] S, IsPettisIsotypicAverageOn μ₁ univ τ ω A :=
    (existsUnique_compactActionIsotypicAverage (E := S) μ₁ τ hτ
      schwartzBruhat_bornological (hseq (fun k f ↦ τ k f) hτ) ω).exists
  obtain ⟨A, hA⟩ := hex
  let P : S →L[ℂ] S := (μ₁.real univ)⁻¹ • A
  have hP (f : S) (x : G) :
      P f x = (μ₁.real univ)⁻¹ •
        ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁ := by
    let ev : StrongDual ℂ S :=
      ⟨(LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype,
        continuous_schwartzBruhat_eval x⟩
    have hIntegral : HasPettisIntegral (.positive (μ₁.restrict univ))
        (fun k : K ↦ star (ω k : ℂ) • τ k f) (A f) := hA f
    unfold HasPettisIntegral at hIntegral
    obtain ⟨_, h⟩ := hIntegral
    have he := congrArg (fun z : PettisWeakCompletion S ↦
      (show Module.Dual ℂ (StrongDual ℂ S) from z) ev) h
    let F : K → ℂ := fun k ↦ star (ω k : ℂ) * (τ k f) x
    change A f x = ∫ k, F k ∂(μ₁.restrict univ) at he
    have hpointwise (k : K) : (τ k f) x = f ((k : G)⁻¹ * x) :=
      congrArg (fun g : S ↦ g x) (hρ k f)
    have hscalar := calc
      A f x = ∫ k, F k ∂(μ₁.restrict univ) := he
      _ = ∫ k, F k ∂μ₁ :=
        congrArg (fun ν : Measure K ↦ ∫ k, F k ∂ν) Measure.restrict_univ
      _ = ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁ :=
        integral_congr_ae (ae_of_all _ fun k ↦ congrArg (star (ω k : ℂ) * ·) (hpointwise k))
    exact congrArg ((μ₁.real univ)⁻¹ • ·) hscalar
  refine ⟨P, hP, fun Q hQ ↦ ContinuousLinearMap.ext fun f ↦ ?_⟩
  exact Subtype.ext (funext fun x ↦ (hQ f x).trans (hP f x).symm)

/-- Paper: (D.2.1.2), p. 792. The Schwartz–Bruhat projector is the
continuous linear operator given by the normalized fiber integral. -/
def schwartzBruhatIsotypicProjector (ω : PontryaginDual K) : S →L[ℂ] S :=
  Classical.choose (existsUnique_schwartzBruhatIsotypicProjector m hm μ₁ ω).exists

omit hm hμ₁ [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
/-- Schwartz–Bruhat functions are continuous because every elementary stage realization is
continuous. -/
private theorem continuous_schwartzBruhat (f : S) : Continuous (fun x ↦ f x) := by
  classical
  let C := (ContinuousMap.coeFnLinearMap ℂ (α := G) (M := ℂ)).range
  suffices hle : schwartzBruhatSubmodule G ≤ C by
    obtain ⟨g, hg⟩ := hle (show (fun x ↦ f x) ∈ schwartzBruhatSubmodule G from
      (show schwartzBruhatSubmodule G from f).property)
    exact hg ▸ g.continuous
  unfold schwartzBruhatSubmodule
  refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
  rintro _ ⟨s, rfl⟩
  refine ⟨⟨_, ?_⟩, rfl⟩
  let _ := e.finiteGroup
  have htorus : IsOpenQuotientMap
      (fun t : EuclideanSpace ℝ (Fin e.torusDim) ↦ fun i ↦ (t i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin e.torusDim ↦ ℝ)).isOpenQuotientMap
  have hcover := (IsOpenQuotientMap.id (X := EuclideanSpace ℝ (Fin e.realDim))).prodMap htorus
  have hfiber (z : Fin e.latticeRank → ℤ) (b : Fin e.finiteOrder) :
      Continuous (fun xt : EuclideanSpace ℝ (Fin e.realDim) × (Fin e.torusDim → AddCircle (1 : ℝ)) ↦
        s (xt.1, xt.2, z, b)) :=
    hcover.continuous_comp_iff.mp (s.property.1 z b).continuous
  have hs : Continuous (fun g ↦ s g) := by
    rw [← (Homeomorph.prodAssoc _ _ _).isOpenQuotientMap.continuous_comp_iff,
      continuous_iff_continuousAt]
    rintro ⟨xt, z, b⟩
    exact continuousAt_prod_of_discrete_right.mpr (hfiber z b).continuousAt
  have hopen := a.property.1
  have hclosed := a.val.1.isClosed_of_isOpen hopen
  rw [← continuousOn_univ, ← union_compl_self (a.val.1 : Set G),
    continuousOn_union_iff_of_isOpen hopen hclosed.isOpen_compl]
  constructor
  · rw [continuousOn_iff_continuous_domRestrict]
    refine (hs.comp (e.equiv.continuous.comp QuotientGroup.continuous_mk)).congr fun y ↦ ?_
    change s (Multiplicative.toAdd (e.equiv (QuotientGroup.mk y))) =
      schwartzBruhatStageRealization a e s (y : G)
    rw [schwartzBruhatStageRealization_apply, dite_eq_left y.property]
  · apply continuousOn_const.congr
    intro y hy
    change schwartzBruhatStageRealization a e s y = 0
    rw [schwartzBruhatStageRealization_apply]
    exact dite_eq_right (show y ∉ a.val.1 from hy)

/-- Paper: (D.2.1.2), p. 792. The kernel orbit is integrable at
each evaluation point, where the projector agrees with the stated integral. -/
theorem schwartzBruhatIsotypicProjector_apply (ω : PontryaginDual K) (f : S) (x : G) :
    Integrable (fun k : K ↦ star (ω k : ℂ) * f ((k : G)⁻¹ * x)) μ₁ ∧
    schwartzBruhatIsotypicProjector m hm μ₁ ω f x = (μ₁.real univ)⁻¹ •
      ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁ := by
  refine ⟨?_, (Classical.choose_spec
    (existsUnique_schwartzBruhatIsotypicProjector m hm μ₁ ω).exists) f x⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have hχ : Continuous (fun k : K ↦ star (ω k : ℂ)) := by fun_prop
  have hshift : Continuous (fun k : K ↦ (k : G)⁻¹ * x) :=
    continuous_subtype_val.inv.mul continuous_const
  exact (hχ.mul ((continuous_schwartzBruhat f).comp hshift)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Paper: (D.2.1.2), p. 792. On an isotypic vector, the normalized average
recovers the vector. -/
theorem schwartzBruhatIsotypicProjector_apply_isotype (ω : PontryaginDual K) (f : S)
    (hf : f ∈ actionIsotype ρS ω) :
    schwartzBruhatIsotypicProjector m hm μ₁ ω f = f := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  refine Subtype.ext (funext fun x ↦ ?_)
  change schwartzBruhatIsotypicProjector m hm μ₁ ω f x = f x
  have hconstant (k : K) : star (ω k : ℂ) * f ((k : G)⁻¹ * x) = f x := by
    have h := congrArg (fun g : S ↦ g x) ((mem_actionIsotype ρS ω f).mp hf k)
    change schwartzBruhatTranslationAction (G := G) (k : G) f x = (ω k : ℂ) * f x at h
    rw [schwartzBruhatTranslationAction_apply (k : G) x f] at h
    rw [h, ← mul_assoc]
    simp [← Circle.coe_inv_eq_conj]
  rw [(schwartzBruhatIsotypicProjector_apply m hm μ₁ ω f x).2,
    integral_congr_ae (ae_of_all μ₁ hconstant), integral_const]
  exact inv_smul_smul₀ (measureReal_univ_ne_zero (μ := μ₁)) (f x)

/-- Paper: (D.2.2.1), p. 794. Averaging identifies the Hausdorff quotient
with the corresponding subspace of homogeneous Schwartz–Bruhat functions. -/
theorem schwartzBruhatIsotypicProjector_quotient_equiv (ω : PontryaginDual K) :
    let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
    ∃ e : (S ⧸ P.ker) ≃L[ℂ] actionIsotype ρS ω,
      ∀ f : S, (e (P.ker.mkQ f) : S) = P f := by sorry

end Projector

section CoarserTopology

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [hE : CompleteSpace E]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
  (μ₁ : Measure m.toMonoidHom.ker) [hμ₁ : μ₁.IsHaarMeasure]

local notation "K" => m.toMonoidHom.ker
local notation "S" => SchwartzBruhat G
local notation "ρS" => MonoidHom.comp (schwartzBruhatTranslationAction (G := G)) (Subgroup.subtype K)

variable (ρ : G →* (E →L[ℂ] E))
  (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
  (heq : EquicontinuousAt (fun g : G ↦ (ρ g : E → E)) 0)
  (i : SchwartzBruhat G →L[ℂ] E) (hi : Injective i)
  (hcomm : ∀ (g : G) (f : SchwartzBruhat G),
    i (schwartzBruhatTranslationAction (G := G) g f) = ρ g (i f))

local notation "ρE" => MonoidHom.comp ρ (Subgroup.subtype K)

include hE hμ₁ hρ heq hm in
/-- Paper: (D.2.2.4), p. 794. The complete target admits a unique normalized
Pettis projector for the action of the norm-one group with the chosen character. -/
theorem existsUnique_modulatedActionIsotypicProjector (ω : PontryaginDual K) :
    ∃! Q : E →L[ℂ] E, IsPettisIsotypicAverageOn μ₁ univ ρE ω (μ₁.real univ • Q) := by sorry

variable (ω : PontryaginDual m.toMonoidHom.ker) (Q : E →L[ℂ] E)
  (hQ : IsPettisIsotypicAverageOn μ₁ univ (ρ.comp m.toMonoidHom.ker.subtype) ω (μ₁.real univ • Q))

local notation "P" => schwartzBruhatIsotypicProjector m hm μ₁ ω

include hE hρ heq hi hcomm hQ

/-- Paper: Lemma D.2.2.1(1), p. 795. The kernel of averaging on the target
pulls back to the kernel of averaging on the source. -/
theorem schwartzBruhatIsotype_comap_ker : Q.ker.comap i.toLinearMap = (P).ker := by sorry

/-- Paper: Lemma D.2.2.1(1), p. 795. The injection gives a continuous
linear injection on the quotients by the averaging kernels. -/
theorem schwartzBruhatIsotype_quotient_map :
    ∃ j : (S ⧸ (P).ker) →L[ℂ] (E ⧸ Q.ker), Injective j ∧
      ∀ f : S, j ((P).ker.mkQ f) = Q.ker.mkQ (i f) := by sorry

/-- Paper: Lemma D.2.2.1(1), p. 795. The injection restricts to a
continuous linear injection on the homogeneous subspaces. -/
theorem schwartzBruhatIsotype_subspace_map :
    ∃ j : actionIsotype ρS ω →L[ℂ] actionIsotype ρE ω,
      Injective j ∧ ∀ f, (j f : E) = i (f : S) := by sorry

/-- Paper: Lemma D.2.2.1(2), p. 795. The inverse image of the target
isotype is the source isotype. -/
theorem schwartzBruhatIsotype_comap : (actionIsotype ρE ω).comap i.toLinearMap =
    actionIsotype ρS ω := by sorry

/-- Paper: Lemma D.2.2.1(3), p. 795. A dense injection induces a
dense map of isotypic quotients. -/
theorem schwartzBruhatIsotype_quotient_map_dense (hd : DenseRange i)
    (j : (S ⧸ (P).ker) →L[ℂ] (E ⧸ Q.ker))
    (hj : ∀ f : S, j ((P).ker.mkQ f) = Q.ker.mkQ (i f)) :
    DenseRange j := by sorry

/-- Paper: Lemma D.2.2.1(3), p. 795. A dense injection induces a
dense map of isotypic subspaces. -/
theorem schwartzBruhatIsotype_subspace_map_dense (hd : DenseRange i)
    (j : actionIsotype ρS ω →L[ℂ] actionIsotype ρE ω)
    (hj : ∀ f, (j f : E) = i (f : S)) :
    DenseRange j := by sorry

omit hQ hρ heq hcomm in
/-- Paper: Lemma D.2.2.1(4), p. 795. An endomorphism continuous
for the topology induced by a dense injection extends uniquely to the
complete target space. -/
theorem schwartzBruhat_dense_extension (hd : DenseRange i) (T : S →L[ℂ] S)
    (hT : @Continuous S E (TopologicalSpace.induced i inferInstance) _
      (fun f ↦ i (T f))) :
    ∃! U : E →L[ℂ] E, ∀ f : S, U (i f) = i (T f) := by sorry

/-- Paper: Lemma D.2.2.1(4), p. 795. The extension inherits the
intertwining relation on the norm-one subgroup. The intertwiner and
its extension induce unique maps on the isotypic quotients, with
the same commuting relations on the homogeneous subspaces. The character
condition specifies pullback by the inverse of the restricted automorphism. -/
theorem schwartzBruhatIsotype_extension_intertwines (hd : DenseRange i)
    (T : S →L[ℂ] S) (U : E →L[ℂ] E) (hU : ∀ f : S, U (i f) = i (T f))
    (α : G ≃ₜ* G) (hα : ∀ g : G, m (α g) = m g)
    (hT : ∀ (k : K) (f : S),
      T (ρS k f) = schwartzBruhatTranslationAction (G := G) (α (k : G)) (T f))
    (χ : PontryaginDual K)
    (hχ : ∀ k k' : K, (k' : G) = α (k : G) → χ k' = ω k)
    (Q' : E →L[ℂ] E)
    (hQ' : IsPettisIsotypicAverageOn μ₁ univ ρE χ (μ₁.real univ • Q')) :
    (∀ (k : K) (u : E), U (ρE k u) = ρ (α (k : G)) (U u)) ∧
    let P' := schwartzBruhatIsotypicProjector m hm μ₁ χ
    ∃! w : ((S ⧸ (P).ker) →L[ℂ] (S ⧸ P'.ker)) × ((E ⧸ Q.ker) →L[ℂ] (E ⧸ Q'.ker)),
      (∀ f : S, w.1 ((P).ker.mkQ f) = P'.ker.mkQ (T f) ∧ T (P f) = P' (T f)) ∧
      (∀ u : E, w.2 (Q.ker.mkQ u) = Q'.ker.mkQ (U u) ∧ U (Q u) = Q' (U u)) ∧
      ∀ f : S, w.2 (Q.ker.mkQ (i f)) = Q'.ker.mkQ (i (T f)) := by sorry

end CoarserTopology

section SplitModule

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local instance {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}
    (p : SeminormFamily ℂ X ι) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)

local notation "K" => m.toMonoidHom.ker
local notation "Γ" => m.toMonoidHom.range
local notation "S" => SchwartzBruhat G
local notation "SΓ" => SchwartzBruhat Γ
local notation "HS" => InductiveTensor (SchwartzBruhat K) SΓ

include hm

/-- Paper: Lemma D.2.2.2(1), p. 796. A section induces the Schwartz–Bruhat
tensor isomorphism. On pure tensors its evaluations are products in the
split coordinates. It intertwines the two actions by left translation. -/
theorem schwartzBruhat_modulation_tensor (τ : Γ →ₜ* G)
    (hτ : ∀ t, m (τ t) = (t : ℝ≥0ˣ)) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    letI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
    letI : SecondCountableTopology ℝ≥0ˣ :=
      (Units.isEmbedding_val₀ (G₀ := ℝ≥0)).secondCountableTopology
    letI : SecondCountableTopology Γ := TopologicalSpace.Subtype.secondCountableTopology (Γ : Set ℝ≥0ˣ)
    letI : LocallyCompactSpace Γ := hm.isClosed_range.locallyCompactSpace
    ∃ e : Completion HS ≃L[ℂ] S,
      (∀ (f : SchwartzBruhat K) (h : SΓ) (k : K) (t : Γ),
        e (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h)) ((k : G) * τ t) = f k * h t) ∧
      ∀ (k : K) (t : Γ) (z : Completion HS),
        e (Completion.map (inductiveTensorMap
          ((schwartzBruhatTranslationAction (G := K)) k).toLinearMap
          ((schwartzBruhatTranslationAction (G := Γ)) t).toLinearMap : HS → HS) z) =
        schwartzBruhatTranslate ((k : G) * τ t) (e z) := by sorry

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [hE : CompleteSpace E]
  [MeasurableSpace G] [BorelSpace G]
  (μ₁ : Measure m.toMonoidHom.ker) [hμ₁ : μ₁.IsHaarMeasure]
  (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
  (i : SchwartzBruhat G →L[ℂ] E) (hi : Injective i) (hd : DenseRange i)
  (hcomm : ∀ (g : G) (f : SchwartzBruhat G),
    i (schwartzBruhatTranslationAction (G := G) g f) = ρ g (i f))

include hE hμ₁ hρ hi hd hcomm

/-- Paper: Lemma D.2.2.2(2), p. 796. The profile space with the
topology induced by its pullback to the dense subspace completes,
via character multiplication, to the isotypic quotient of the target. -/
theorem schwartzBruhat_modulation_isotype_completion
    (τ : Γ →ₜ* G) (hτ : ∀ t, m (τ t) = (t : ℝ≥0ˣ))
    (hborn : ∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p)
    (hseq : ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
      TendstoUniformly (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop)
    (hmul : ∀ χ : PontryaginDual G, ∃ M : S →L[ℂ] S,
      (∀ (f : S) (x : G), M f x = (χ x : ℂ) * f x) ∧
      @Continuous S E (TopologicalSpace.induced i inferInstance) _ (fun f ↦ i (M f)))
    (ω : PontryaginDual K) :
    ∃ (Q : E →L[ℂ] E) (j w : SΓ →L[ℂ] S),
      IsPettisIsotypicAverageOn μ₁ univ (ρ.comp (Subgroup.subtype K)) ω
        (μ₁.real univ • Q) ∧
      (∀ (f : SΓ) (k : K) (t : Γ),
        j f ((k : G) * τ t) = f t ∧ w f ((k : G) * τ t) = star (ω k : ℂ) * f t) ∧
      let q : SΓ →L[ℂ] E ⧸ Q.ker := Q.ker.mkQL.comp (i.comp w)
      Injective q ∧ DenseRange q ∧
        TopologicalSpace.induced (fun f ↦ i (j f)) inferInstance =
          TopologicalSpace.induced q inferInstance ∧ @CompleteSpace (E ⧸ Q.ker) (IsTopologicalAddGroup.rightUniformSpace _) := by sorry

omit hE hρ hi hd hcomm in
/-- Paper: Corollary D.2.2.3(1), p. 797. For a surjective module,
the Schwartz–Bruhat space of the positive reals maps isomorphically
to the isotypic quotient by pullback and character multiplication. -/
theorem schwartzBruhat_positiveReal_isotype_equiv (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ m) (ω : PontryaginDual K) :
    let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
    ∃ (w : SchwartzBruhat ℝ≥0ˣ →L[ℂ] S)
      (e : SchwartzBruhat ℝ≥0ˣ ≃L[ℂ] (S ⧸ P.ker)),
      (∀ (f : SchwartzBruhat ℝ≥0ˣ) (k : K) (t : ℝ≥0ˣ),
        w f ((k : G) * τ t) = star (ω k : ℂ) * f t) ∧
      ∀ f, e f = P.ker.mkQ (w f) := by sorry

-- TODO(paper-gap): Corollary D.2.2.3(2) drops the density hypothesis.
-- For the trivial character, the injection into S(G) × ℂ with zero
-- second coordinate leaves the added trivial summand outside the closure.

end SplitModule

end RiemannMasullo
