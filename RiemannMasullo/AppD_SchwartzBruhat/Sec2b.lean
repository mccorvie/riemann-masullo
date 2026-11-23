module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1d
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Compact

/-! # Schwartz–Bruhat isotypes and coarser topologies -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology UniformSpace
open scoped NNReal TensorProduct

section SchwartzBruhatAction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G] [hSC : SecondCountableTopology G]

-- The unused-section-variable check repeatedly traverses the instance terms in
-- SchwartzBruhat. Scope the option to the expensive declarations.
set_option linter.unusedSectionVars false in
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

set_option linter.unusedSectionVars false in
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

set_option linter.unusedSectionVars false in
omit hm in
/-- On a compact kernel the character-twisted orbits admit a continuous
Schwartz–Bruhat Pettis average. -/
private theorem exists_schwartzBruhatPettisIsotypicAverage (hcompact : CompactSpace K)
    (ω : PontryaginDual K) :
    ∃ A : S →L[ℂ] S, IsPettisIsotypicAverageOn μ₁ univ ρS ω A := by
  have : CompactSpace K := hcompact
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
  exact (existsUnique_compactActionIsotypicAverage (E := S) μ₁ τ hτ
    schwartzBruhat_bornological (hseq (fun k f ↦ τ k f) hτ) ω).exists

set_option linter.unusedSectionVars false in
/-- Paper: (D.2.1.1), pp. 792–793. The normalized Pettis average on the
Schwartz–Bruhat space satisfies the scalar integral formula at each point. -/
private theorem exists_schwartzBruhatIsotypicProjector_average (ω : PontryaginDual K) :
    ∃ P : S →L[ℂ] S,
      (∀ (f : S) (x : G), P f x = (μ₁.real univ)⁻¹ •
        ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁) ∧
      IsPettisIsotypicAverageOn μ₁ univ ρS ω (μ₁.real univ • P) := by
  letI hcompact : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have hex : ∃ A : S →L[ℂ] S, IsPettisIsotypicAverageOn μ₁ univ ρS ω A :=
    exists_schwartzBruhatPettisIsotypicAverage (G := G) m μ₁ hcompact ω
  obtain ⟨A, hA⟩ := hex
  let P : S →L[ℂ] S := (μ₁.real univ)⁻¹ • A
  have hP (f : S) (x : G) :
      P f x = (μ₁.real univ)⁻¹ •
        ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁ := by
    let ev : StrongDual ℂ S :=
      ⟨(LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype,
        continuous_schwartzBruhat_eval x⟩
    have hIntegral : HasPettisIntegral (.positive (μ₁.restrict univ))
        (fun k : K ↦ star (ω k : ℂ) • ρS k f) (A f) := hA f
    unfold HasPettisIntegral at hIntegral
    obtain ⟨_, h⟩ := hIntegral
    have he := congrArg (fun z : PettisWeakCompletion S ↦
      (show Module.Dual ℂ (StrongDual ℂ S) from z) ev) h
    let F : K → ℂ := fun k ↦ star (ω k : ℂ) * (ρS k f) x
    change A f x = ∫ k, F k ∂(μ₁.restrict univ) at he
    have hpointwise (k : K) : (ρS k f) x = f ((k : G)⁻¹ * x) :=
      schwartzBruhatTranslationAction_apply (k : G) x f
    have hscalar := calc
      A f x = ∫ k, F k ∂(μ₁.restrict univ) := he
      _ = ∫ k, F k ∂μ₁ :=
        congrArg (fun ν : Measure K ↦ ∫ k, F k ∂ν) Measure.restrict_univ
      _ = ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁ :=
        integral_congr_ae (ae_of_all _ fun k ↦ congrArg (star (ω k : ℂ) * ·) (hpointwise k))
    exact congrArg ((μ₁.real univ)⁻¹ • ·) hscalar
  have hmass : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  exact ⟨P, hP, by simpa only [P, smul_inv_smul₀ hmass] using hA⟩

set_option linter.unusedSectionVars false in
/-- Paper: (D.2.1.1), pp. 792–793. The normalized character average exists
as a continuous linear endomorphism of the Schwartz–Bruhat space. -/
theorem existsUnique_schwartzBruhatIsotypicProjector (ω : PontryaginDual K) :
    ∃! P : S →L[ℂ] S, ∀ (f : S) (x : G),
      P f x = (μ₁.real univ)⁻¹ •
        ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂μ₁ := by
  refine (exists_schwartzBruhatIsotypicProjector_average m hm μ₁ (hμ₁ := hμ₁) ω).elim
    fun P hP ↦ ⟨P, hP.1, fun Q hQ ↦ ContinuousLinearMap.ext fun f ↦ ?_⟩
  exact Subtype.ext (funext fun x ↦ (hQ f x).trans (hP.1 f x).symm)

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
  have htorus : IsOpenQuotientMap
      (fun t : EuclideanSpace ℝ (Fin e.torusDim) ↦ fun i ↦ (t i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin e.torusDim ↦ ℝ)).isOpenQuotientMap
  have hcover := (IsOpenQuotientMap.id (X := EuclideanSpace ℝ (Fin e.realDim))).prodMap htorus
  have hfiber (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
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

set_option linter.unusedSectionVars false in
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
      ∀ f : S, (e (P.ker.mkQ f) : S) = P f := by
  let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
  let H := actionIsotype ρS ω
  let integrand (f : S) (x : G) (k : K) : ℂ := star (ω k : ℂ) * f ((k : G)⁻¹ * x)
  have hP (f : S) (x : G) : P f x = (μ₁.real univ)⁻¹ • ∫ k, integrand f x k ∂μ₁ :=
    (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω f x).2
  have hchar (k : K) : (ω k : ℂ) * star (ω k : ℂ) = 1 := by
    have hconj : star (ω k : ℂ) = (ω k : ℂ)⁻¹ := (Circle.coe_inv_eq_conj (ω k)).symm
    rw [hconj, mul_inv_cancel₀ (Circle.coe_ne_zero (ω k))]
  have hmem (f : S) : P f ∈ H := by
    apply (mem_actionIsotype ..).2
    intro k
    refine Subtype.ext (funext fun x ↦ ?_)
    change schwartzBruhatTranslationAction (G := G) (k : G) (P f) x = (ω k : ℂ) • P f x
    let shifted (g : K) : ℂ := (ω k : ℂ) * integrand f x g
    have hshift : (∫ g, integrand f ((k : G)⁻¹ * x) g ∂μ₁) =
        (ω k : ℂ) * (∫ g, integrand f x g ∂μ₁) := calc
      _ = ∫ g, shifted (k * g) ∂μ₁ := by
        refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
        simp only [shifted, integrand, Subgroup.coe_mul, mul_inv_rev, mul_assoc, map_mul,
          Circle.coe_mul, star_mul']
        rw [← mul_assoc (ω k : ℂ), hchar k, one_mul]
      _ = ∫ g, shifted g ∂μ₁ := integral_mul_left_eq_self shifted k
      _ = _ := integral_const_mul (ω k : ℂ) (integrand f x)
    calc
      _ = P f ((k : G)⁻¹ * x) := schwartzBruhatTranslationAction_apply (k : G) x (P f)
      _ = (μ₁.real univ)⁻¹ • (∫ g, integrand f ((k : G)⁻¹ * x) g ∂μ₁) := hP f _
      _ = (μ₁.real univ)⁻¹ • ((ω k : ℂ) • ∫ g, integrand f x g ∂μ₁) :=
        congrArg ((μ₁.real univ)⁻¹ • ·) hshift
      _ = (ω k : ℂ) • ((μ₁.real univ)⁻¹ • ∫ g, integrand f x g ∂μ₁) := smul_comm _ _ _
      _ = _ := congrArg ((ω k : ℂ) • ·) (hP f x).symm
  have hfix (f : S) (hf : f ∈ H) : P f = f := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    have hmass : μ₁.real univ ≠ 0 := (measureReal_univ_pos (μ := μ₁)).ne'
    refine Subtype.ext (funext fun x ↦ ?_)
    change P f x = f x
    refine (hP f x).trans ?_
    have horbit (k : K) : f ((k : G)⁻¹ * x) = (ω k : ℂ) * f x := by
      have hk := congrArg (fun g : S ↦ g x) ((mem_actionIsotype ..).1 hf k)
      change schwartzBruhatTranslationAction (G := G) (k : G) f x = (ω k : ℂ) * f x at hk
      exact (schwartzBruhatTranslationAction_apply (k : G) x f).symm.trans hk
    have hintegrand (k : K) : integrand f x k = f x := by
      change star (ω k : ℂ) * f ((k : G)⁻¹ * x) = f x
      rw [horbit k, ← mul_assoc, mul_comm (star (ω k : ℂ)), hchar k, one_mul]
    calc
      _ = (μ₁.real univ)⁻¹ • (∫ _ : K, f x ∂μ₁) :=
        congrArg ((μ₁.real univ)⁻¹ • ·) (integral_congr_ae (ae_of_all _ hintegrand))
      _ = f x := by rw [integral_const, smul_smul, inv_mul_cancel₀ hmass, one_smul]
  let A := P.codRestrict H hmem
  let F := P.ker.liftQL A (fun _ hf ↦ Subtype.ext (show P _ = 0 from hf))
  let J := P.ker.mkQL.comp H.subtypeL
  have hleft : LeftInverse J F := by
    refine (P.ker.mkQ_surjective.forall (p := fun q ↦ J (F q) = q)).2 fun f ↦ ?_
    change P.ker.mkQ (P f) = P.ker.mkQ f
    apply (Submodule.Quotient.eq P.ker).2
    change P (P f - f) = 0
    exact (map_sub P (P f) f).trans (sub_eq_zero.mpr (hfix (P f) (hmem f)))
  have hright : RightInverse J F := fun f ↦ Subtype.ext (hfix f f.property)
  exact ⟨ContinuousLinearEquiv.equivOfInverse F J hleft hright, fun _ ↦ rfl⟩

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
    ∃! Q : E →L[ℂ] E, IsPettisIsotypicAverageOn μ₁ univ ρE ω (μ₁.real univ • Q) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let τ : K →* (E →L[ℂ] E) :=
    { toFun := fun k ↦ star (ω k : ℂ) • ρE k
      map_one' := by simp
      map_mul' := fun k l ↦ by
        simp only [map_mul, Circle.coe_mul, star_mul', smul_mul_smul_comm] }
  have hτ_apply (k : K) (u : E) : τ k u = star (ω k : ℂ) • ρE k u := rfl
  have hτ : Continuous (fun p : K × E ↦ τ p.1 p.2) :=
    (show Continuous (fun p : K × E ↦ star (ω p.1 : ℂ)) from by fun_prop).smul
      (hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  have hτeq : EquicontinuousAt (fun k : K ↦ (τ k : E → E)) 0 := by
    have basis := (nhds_basis_balanced ℂ E).uniformity_of_nhds_zero
    apply basis.equicontinuousAt_iff_right.mpr
    intro U hU
    filter_upwards [basis.equicontinuousAt_iff_right.mp heq U hU] with u hu k
    have hk : ρ (k : G) u ∈ U := by simpa using hu (k : G)
    change τ k u - τ k 0 ∈ U
    rw [map_zero, sub_zero]
    exact hU.2.smul_mem (by simp [← Circle.coe_inv_eq_conj]) hk
  have hAvg : ∃! A : E →L[ℂ] E, IsPettisIsotypicAverageOn μ₁ univ ρE ω A := by
    simpa only [IsPettisIsotypicAverageOn, PontryaginDual.one_apply, Circle.coe_one,
      star_one, one_smul, hτ_apply]
      using existsUnique_compactActionAverage μ₁ τ hτ (Or.inl hτeq)
  obtain ⟨A, hA, huniq⟩ := hAvg
  have hmass : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  refine ⟨(μ₁.real univ)⁻¹ • A, ?_, ?_⟩
  · simpa only [smul_inv_smul₀ hmass] using hA
  · intro Q hQ
    apply smul_right_injective _ hmass
    simpa only [smul_inv_smul₀ hmass] using huniq _ hQ

variable (ω : PontryaginDual m.toMonoidHom.ker) (Q : E →L[ℂ] E)
  (hQ : IsPettisIsotypicAverageOn μ₁ univ (ρ.comp m.toMonoidHom.ker.subtype) ω (μ₁.real univ • Q))

local notation "P" => schwartzBruhatIsotypicProjector m hm μ₁ ω

/-- A continuous linear functional evaluates a Pettis integral over the whole
space as a scalar integral. -/
private theorem pettisIntegral_univ_eval {X V : Type*} [MeasurableSpace X]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {μ : Measure X} {F : X → V} {a : V}
    (h : HasPettisIntegral (.positive (μ.restrict univ)) F a) (φ : StrongDual ℂ V) :
    φ a = ∫ x, φ (F x) ∂μ := by
  obtain ⟨_, he⟩ := h
  have h := LinearMap.congr_fun he φ
  change φ a = ∫ x, φ (F x) ∂(μ.restrict univ) at h
  rwa [Measure.restrict_univ] at h

set_option linter.unusedSectionVars false in
include hcomm hQ in
/-- Paper: Lemma D.2.2.1, p. 795. An equivariant continuous linear map
from the Schwartz–Bruhat space intertwines the normalized Pettis averages. -/
private theorem schwartzBruhatIsotypicProjector_intertwines (f : S) : i (P f) = Q (i f) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  have hmass : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  refine (exists_schwartzBruhatIsotypicProjector_average m hm μ₁ (hμ₁ := hμ₁) ω).elim ?_
  intro A hA
  have hUnique := existsUnique_schwartzBruhatIsotypicProjector m hm μ₁ (hμ₁ := hμ₁) ω
  have hproj : A = P := hUnique.unique hA.1 (Classical.choose_spec hUnique.exists)
  have havg : i ((μ₁.real univ • A) f) = (μ₁.real univ • Q) (i f) := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro φ
    let F (k : K) : ℂ := φ (star (ω k : ℂ) • ρE k (i f))
    calc
      φ (i ((μ₁.real univ • A) f)) = ∫ k : K, φ (i (star (ω k : ℂ) • ρS k f)) ∂μ₁ :=
        pettisIntegral_univ_eval (hA.2 f) (φ.comp i)
      _ = ∫ k, F k ∂μ₁ := integral_congr_ae (ae_of_all _ fun k ↦ by
        refine congrArg φ ((i.map_smul (star (ω k : ℂ)) (ρS k f)).trans ?_)
        exact congrArg (fun v : E ↦ star (ω k : ℂ) • v) (hcomm (k : G) f))
      _ = φ ((μ₁.real univ • Q) (i f)) := (pettisIntegral_univ_eval (hQ (i f)) φ).symm
  refine (congrArg (fun L : S →L[ℂ] S ↦ i (L f)) hproj.symm).trans ?_
  exact smul_right_injective E hmass ((i.map_smul_of_tower (μ₁.real univ) (A f)).symm.trans havg)

include hE hρ heq hi hcomm hQ

-- Retain the existing section hypotheses in the theorem signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.2.2.1(1), p. 795. The kernel of averaging on the target
pulls back to the kernel of averaging on the source. -/
theorem schwartzBruhatIsotype_comap_ker : Q.ker.comap i.toLinearMap = (P).ker := by
  refine Submodule.ext fun f ↦ ?_
  change Q (i f) = 0 ↔ P f = 0
  have hf : i (P f) = Q (i f) :=
    schwartzBruhatIsotypicProjector_intertwines m hm μ₁ ρ i hcomm ω Q hQ f
  exact ⟨fun h ↦ hi (hf.trans (h.trans i.map_zero.symm)),
    fun h ↦ hf.symm.trans ((congrArg i h).trans i.map_zero)⟩

set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.2.2.1(1), p. 795. The injection gives a continuous
linear injection on the quotients by the averaging kernels. -/
theorem schwartzBruhatIsotype_quotient_map :
    ∃ j : (S ⧸ (P).ker) →L[ℂ] (E ⧸ Q.ker), Injective j ∧
      ∀ f : S, j ((P).ker.mkQ f) = Q.ker.mkQ (i f) := by
  let F := Q.ker.mkQL.comp i
  have hker : (P).ker = F.ker := calc
    (P).ker = Q.ker.comap i.toLinearMap :=
      (schwartzBruhatIsotype_comap_ker m hm μ₁ ρ hρ heq i hi hcomm ω Q hQ).symm
    _ = (Q.ker.mkQ.ker).comap i.toLinearMap :=
      congrArg (Submodule.comap i.toLinearMap) (Submodule.ker_mkQ Q.ker).symm
    _ = F.ker := (LinearMap.ker_comp i.toLinearMap Q.ker.mkQ).symm
  refine ⟨(P).ker.liftQL F hker.le, ?_, fun _ ↦ rfl⟩
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' (P).ker F.toLinearMap hker)

-- Retain the existing section hypotheses in the theorem signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.2.2.1(1), p. 795. The injection restricts to a
continuous linear injection on the homogeneous subspaces. -/
theorem schwartzBruhatIsotype_subspace_map :
    ∃ j : actionIsotype ρS ω →L[ℂ] actionIsotype ρE ω,
      Injective j ∧ ∀ f, (j f : E) = i (f : S) := by
  have hmem : ∀ f ∈ actionIsotype ρS ω, i f ∈ actionIsotype ρE ω := by
    intro f hf
    apply (mem_actionIsotype ρE ω (i f)).2
    intro k
    calc
      ρE k (i f) = i (ρS k f) := (hcomm (k : G) f).symm
      _ = i ((ω k : ℂ) • f) := congrArg i ((mem_actionIsotype ρS ω f).1 hf k)
      _ = (ω k : ℂ) • i f := map_smul i _ _
  refine ⟨i.restrict hmem, ?_, fun _ ↦ rfl⟩
  intro f g hfg
  exact Subtype.ext (hi (congrArg Subtype.val hfg))

omit hE hρ heq hi hcomm hQ in
/-- An injective equivariant map pulls back each target isotype to the source isotype. -/
private theorem actionIsotype_comap_of_injective {H X Y : Type*} [Monoid H] [TopologicalSpace H]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (σ : H →* (X →L[ℂ] X)) (τ : H →* (Y →L[ℂ] Y)) (χ : PontryaginDual H)
    (j : X →L[ℂ] Y) (hj : Injective j) (h : ∀ k x, j (σ k x) = τ k (j x)) :
    (actionIsotype τ χ).comap j.toLinearMap = actionIsotype σ χ := by
  refine Submodule.ext fun x ↦ ?_
  change j x ∈ actionIsotype τ χ ↔ x ∈ actionIsotype σ χ
  simp only [mem_actionIsotype]
  refine forall_congr' fun k ↦ ?_
  rw [← h k x, ← j.map_smul]
  exact hj.eq_iff

-- Retain the existing hypotheses from the averaging setup in the signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.2.2.1(2), p. 795. The inverse image of the target
isotype is the source isotype. -/
theorem schwartzBruhatIsotype_comap : (actionIsotype ρE ω).comap i.toLinearMap =
    actionIsotype ρS ω := by
  refine actionIsotype_comap_of_injective (H := K) (X := S) (Y := E) ρS ρE ω i hi ?_
  intro k f
  exact hcomm (k : G) f

set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.2.2.1(3), p. 795. A dense injection induces a
dense map of isotypic quotients. -/
theorem schwartzBruhatIsotype_quotient_map_dense (hd : DenseRange i)
    (j : (S ⧸ (P).ker) →L[ℂ] (E ⧸ Q.ker))
    (hj : ∀ f : S, j ((P).ker.mkQ f) = Q.ker.mkQ (i f)) :
    DenseRange j := by
  refine DenseRange.of_comp (g := (P).ker.mkQ) ?_
  have h : (j : _ → _) ∘ (P).ker.mkQ = (Q.ker.mkQ : E → _) ∘ i := funext hj
  rw [h]
  exact Q.ker.mkQ_surjective.denseRange.comp hd Q.ker.continuous_mkQ

omit hE hρ heq hi hcomm hQ in
/-- Equivariant injections with dense range remain dense on the isotypes when the
compact-group averages exist. For infinite Haar measure, weak integrability
of the twisted target orbits forces the target isotype to vanish. -/
private theorem denseRange_isotype_of_pettisAverage
    {H X Y : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [T2Space Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (μ : Measure H) [μ.IsHaarMeasure] (ω : PontryaginDual H)
    (σ : H →* (X →L[ℂ] X)) (τ : H →* (Y →L[ℂ] Y))
    (hτ : Continuous (fun p : H × Y ↦ τ p.1 p.2))
    (B : Y →L[ℂ] Y) (hB : IsPettisIsotypicAverageOn μ univ τ ω B)
    (hcompact : IsFiniteMeasure μ → CompactSpace H)
    (havg : CompactSpace H → ∃ A : X →L[ℂ] X, IsPettisIsotypicAverageOn μ univ σ ω A)
    (i : X →L[ℂ] Y) (hi : Injective i) (hiστ : ∀ (k : H) (f : X), i (σ k f) = τ k (i f))
    (hd : DenseRange i) (j : actionIsotype σ ω →L[ℂ] actionIsotype τ ω)
    (hj : ∀ f, (j f : Y) = i (f : X)) : DenseRange j := by
  have : SeparatingDual ℂ Y := locallyConvexSpace_separatingDual ℂ Y
  by_cases hfinite : IsFiniteMeasure μ
  · have : CompactSpace H := hcompact hfinite
    have hrangeB := compactActionAverage_range μ τ hτ ω B hB
    obtain ⟨A, hA⟩ := havg (inferInstance : CompactSpace H)
    let B' := B.codRestrict (actionIsotype τ ω) (by
      intro u
      rw [← hrangeB]
      exact ⟨u, rfl⟩)
    have hsurj : Surjective B' := by
      intro u
      have hu : (u : Y) ∈ B.toLinearMap.range := hrangeB.symm ▸ u.property
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, Subtype.ext hv⟩
    have havgComm (f : X) : i (A f) = B (i f) := by
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
      intro φ
      obtain ⟨_, hs⟩ := hA f
      obtain ⟨_, ht⟩ := hB (i f)
      have hs' := LinearMap.congr_fun hs (φ.comp i)
      have ht' := LinearMap.congr_fun ht φ
      change φ (i (A f)) = ∫ k : H, φ (i (star (ω k : ℂ) • σ k f))
        ∂(μ.restrict univ) at hs'
      change φ (B (i f)) = ∫ k : H, φ (star (ω k : ℂ) • τ k (i f))
        ∂(μ.restrict univ) at ht'
      have horbit (k : H) : i (σ k f) = τ k (i f) := hiστ k f
      simpa only [map_smul i, horbit, ← ht'] using hs'
    let A' := A.codRestrict (actionIsotype σ ω) (by
      intro f
      apply (mem_actionIsotype σ ω (A f)).2
      intro k
      apply hi
      rw [hiστ, map_smul, havgComm]
      exact ((mem_actionIsotype τ ω _).1 (B' (i f)).property) k)
    have hcomp : (j : _ → _) ∘ A' = (B' : _ → _) ∘ i :=
      funext fun f ↦ Subtype.ext ((hj (A' f)).trans (havgComm f))
    apply DenseRange.of_comp (g := A')
    rw [hcomp]
    exact hsurj.denseRange.comp hd B'.continuous
  · have hzero (u : actionIsotype τ ω) : u = 0 := by
      apply Subtype.ext
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
      intro φ
      have hint := (hB (u : Y)).choose φ
      change Integrable (fun k : H ↦ φ (star (ω k : ℂ) • τ k (u : Y)))
        (μ.restrict univ) at hint
      rw [Measure.restrict_univ] at hint
      have horbit := (mem_actionIsotype τ ω (u : Y)).mp u.property
      have hconst : Integrable (fun _ : H ↦ φ (u : Y)) μ := by
        simpa [horbit, smul_smul, ← Circle.coe_inv_eq_conj] using hint
      simpa only [Submodule.coe_zero, map_zero] using
        (integrable_const_iff.mp hconst).resolve_right hfinite
    exact (show Surjective j from fun u ↦ ⟨0, (j.map_zero).trans (hzero u).symm⟩).denseRange

set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.2.2.1(3), p. 795. A dense injection induces a
dense map of isotypic subspaces. -/
theorem schwartzBruhatIsotype_subspace_map_dense (hd : DenseRange i)
    (j : actionIsotype ρS ω →L[ℂ] actionIsotype ρE ω)
    (hj : ∀ f, (j f : E) = i (f : S)) :
    DenseRange j := by
  have hρK : Continuous (fun p : K × E ↦ ρE p.1 p.2) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hcompact : IsFiniteMeasure μ₁ → CompactSpace K := by
    intro hfinite
    have hclosed : IsClosed (K : Set G) := isClosed_singleton.preimage m.continuous
    have : LocallyCompactSpace K := hclosed.locallyCompactSpace
    have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
    exact compactSpace_of_isFiniteMeasure_haar μ₁
  have havg : CompactSpace K → ∃ A : S →L[ℂ] S, IsPettisIsotypicAverageOn μ₁ univ ρS ω A :=
    fun hc ↦ exists_schwartzBruhatPettisIsotypicAverage (G := G) m μ₁ hc ω
  have hintertwines (k : K) (f : S) : i (ρS k f) = ρE k (i f) := hcomm (k : G) f
  with_reducible
    exact denseRange_isotype_of_pettisAverage (H := K) (X := S) (Y := E) μ₁ ω ρS ρE hρK
      (μ₁.real univ • Q) hQ hcompact havg i hi hintertwines hd j hj

set_option linter.unusedSectionVars false in
omit hQ hρ heq hcomm in
/-- Paper: Lemma D.2.2.1(4), p. 795. An endomorphism continuous
for the topology induced by a dense injection extends uniquely to the
complete target space. -/
theorem schwartzBruhat_dense_extension (hd : DenseRange i) (T : S →L[ℂ] S)
    (hT : @Continuous S E (TopologicalSpace.induced i inferInstance) _
      (fun f ↦ i (T f))) :
    ∃! U : E →L[ℂ] E, ∀ f : S, U (i f) = i (T f) := by
  let R := i.toLinearMap.range
  let e : S ≃ₗ[ℂ] R := LinearEquiv.ofInjective i.toLinearMap hi
  have he (f : S) : (e f : E) = i f := rfl
  have he_cont : @Continuous R S _ (TopologicalSpace.induced i inferInstance) e.symm := by
    apply continuous_induced_rng.mpr
    refine continuous_subtype_val.congr fun x ↦ ?_
    exact (congrArg Subtype.val (e.apply_symm_apply x)).symm.trans (he (e.symm x))
  let F : R →L[ℂ] E := ⟨(i.toLinearMap.comp T.toLinearMap).comp e.symm.toLinearMap,
    @Continuous.comp R S E _ (TopologicalSpace.induced i inferInstance) _
      e.symm (fun f ↦ i (T f)) hT he_cont⟩
  have hdR : DenseRange R.subtypeL := by
    change Dense (Set.range R.subtype)
    rw [← LinearMap.coe_range, Submodule.range_subtype]
    exact hd
  have huR : IsUniformInducing R.subtypeL := ⟨rfl⟩
  have : IsUniformAddGroup R := huR.isUniformAddGroup R.subtypeL
  have hF (f : S) : F (e f) = i (T f) := by
    change i (T (e.symm (e f))) = i (T f)
    exact congrArg (fun g ↦ i (T g)) (e.symm_apply_apply f)
  refine ⟨F.extend R.subtypeL, ?_, ?_⟩
  · intro f
    exact (F.extend_eq hdR huR (e f)).trans (hF f)
  · intro U hU
    refine (F.extend_unique hdR huR U (ContinuousLinearMap.ext ?_)).symm
    intro x
    obtain ⟨f, rfl⟩ := e.surjective x
    exact (hU f).trans (hF f).symm

omit hE hρ heq hi hcomm hQ in
/-- Paper: Lemma D.2.2.1(4), p. 795. Operators that intertwine the projectors
descend uniquely to their kernel quotients. The descended maps agree on the
image of the map relating the two operators. -/
private theorem existsUnique_isotype_quotient_maps {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (P₀ P₁ T : X →L[ℂ] X) (Q₀ Q₁ U : Y →L[ℂ] Y) (j : X →L[ℂ] Y)
    (hTP : ∀ f : X, T (P₀ f) = P₁ (T f)) (hUQ : ∀ u : Y, U (Q₀ u) = Q₁ (U u))
    (hU : ∀ f : X, U (j f) = j (T f)) :
    ∃! w : ((X ⧸ P₀.ker) →L[ℂ] (X ⧸ P₁.ker)) × ((Y ⧸ Q₀.ker) →L[ℂ] (Y ⧸ Q₁.ker)),
      (∀ f : X, w.1 (P₀.ker.mkQ f) = P₁.ker.mkQ (T f) ∧ T (P₀ f) = P₁ (T f)) ∧
      (∀ u : Y, w.2 (Q₀.ker.mkQ u) = Q₁.ker.mkQ (U u) ∧ U (Q₀ u) = Q₁ (U u)) ∧
      ∀ f : X, w.2 (Q₀.ker.mkQ (j f)) = Q₁.ker.mkQ (j (T f)) := by
  let Tq := P₀.ker.liftQL (P₁.ker.mkQL.comp T) (by
    intro f hf
    change P₀ f = 0 at hf
    apply (Submodule.Quotient.mk_eq_zero P₁.ker).2
    change P₁ (T f) = 0
    exact (hTP f).symm.trans ((congrArg T hf).trans (map_zero T)))
  let Uq := Q₀.ker.liftQL (Q₁.ker.mkQL.comp U) (by
    intro u hu
    change Q₀ u = 0 at hu
    apply (Submodule.Quotient.mk_eq_zero Q₁.ker).2
    change Q₁ (U u) = 0
    exact (hUQ u).symm.trans ((congrArg U hu).trans (map_zero U)))
  refine ⟨⟨Tq, Uq⟩, ⟨fun f ↦ ⟨rfl, hTP f⟩, fun u ↦ ⟨rfl, hUQ u⟩,
    fun f ↦ congrArg Q₁.ker.mkQ (hU f)⟩, ?_⟩
  intro w hw
  apply Prod.ext <;> apply ContinuousLinearMap.ext
  · exact (P₀.ker.mkQ_surjective.forall).2 fun f ↦ (hw.1 f).1
  · exact (Q₀.ker.mkQ_surjective.forall).2 fun u ↦ (hw.2.1 u).1

-- Retain the existing section hypotheses in the theorem signature.
set_option maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
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
      ∀ f : S, w.2 (Q.ker.mkQ (i f)) = Q'.ker.mkQ (i (T f)) := by
  have hUE (k : K) (u : E) : U (ρE k u) = ρ (α (k : G)) (U u) := by
    refine hd.induction_on u
      (isClosed_eq (U.continuous.comp (ρE k).continuous)
        ((ρ (α (k : G))).continuous.comp U.continuous)) fun f ↦ ?_
    calc
      U (ρE k (i f)) = U (i (ρS k f)) := congrArg U (hcomm (k : G) f).symm
      _ = i (T (ρS k f)) := hU _
      _ = i (schwartzBruhatTranslationAction (G := G) (α (k : G)) (T f)) :=
        congrArg i (hT k f)
      _ = ρ (α (k : G)) (i (T f)) := hcomm (α (k : G)) (T f)
      _ = ρ (α (k : G)) (U (i f)) := congrArg (ρ (α (k : G))) (hU f).symm
  refine ⟨hUE, ?_⟩
  intro P'
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  have hmass : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  have hi_average (ξ : PontryaginDual K) (B : E →L[ℂ] E)
      (hB : IsPettisIsotypicAverageOn μ₁ univ ρE ξ (μ₁.real univ • B)) (f : S) :
      i (schwartzBruhatIsotypicProjector m hm μ₁ ξ f) = B (i f) :=
    schwartzBruhatIsotypicProjector_intertwines m hm μ₁ ρ i hcomm ξ B hB f
  -- The restricted automorphism preserves Haar measure on the compact kernel.
  have hαker (k : K) : α (k : G) ∈ K :=
    (hα (k : G)).trans k.property
  have hαsymmker (k : K) : α.symm (k : G) ∈ K := by
    change m (α.symm (k : G)) = 1
    rw [← hα (α.symm (k : G)), α.apply_symm_apply]
    exact k.property
  let β : K ≃ₜ* K :=
    { toFun := fun k ↦ ⟨α (k : G), hαker k⟩
      invFun := fun k ↦ ⟨α.symm (k : G), hαsymmker k⟩
      left_inv := fun k ↦ Subtype.ext (α.symm_apply_apply k)
      right_inv := fun k ↦ Subtype.ext (α.apply_symm_apply k)
      map_mul' := fun k l ↦ Subtype.ext (map_mul α (k : G) (l : G))
      continuous_toFun := (α.continuous.comp continuous_subtype_val).subtype_mk hαker
      continuous_invFun := (α.symm.continuous.comp continuous_subtype_val).subtype_mk hαsymmker }
  have hβ : MeasurePreserving β μ₁ μ₁ :=
    β.toMonoidHom.measurePreserving β.continuous β.surjective rfl
  have hUQ (u : E) : U (Q u) = Q' (U u) := by
    apply smul_right_injective E hmass
    change μ₁.real univ • U (Q u) = μ₁.real univ • Q' (U u)
    rw [← U.map_smul_of_tower]
    change U ((μ₁.real univ • Q) u) = (μ₁.real univ • Q') (U u)
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro φ
    let F (k : K) : ℂ := φ (star (χ k : ℂ) • ρE k (U u))
    calc
      φ (U ((μ₁.real univ • Q) u)) =
          ∫ k, φ (U (star (ω k : ℂ) • ρE k u)) ∂μ₁ :=
        pettisIntegral_univ_eval (hQ u) (φ.comp U)
      _ = ∫ k, F (β k) ∂μ₁ := integral_congr_ae (ae_of_all _ fun k ↦ by
        have hk : χ (β k) = ω k := hχ k (β k) rfl
        change φ (U (star (ω k : ℂ) • ρE k u)) =
          φ (star (χ (β k) : ℂ) • ρ (α (k : G)) (U u))
        rw [hk, map_smul, hUE])
      _ = ∫ k, F k ∂μ₁ :=
        hβ.integral_comp β.toHomeomorph.toMeasurableEquiv.measurableEmbedding F
      _ = φ ((μ₁.real univ • Q') (U u)) := (pettisIntegral_univ_eval (hQ' (U u)) φ).symm
  have hTP (f : S) : T (P f) = P' (T f) := by
    apply hi
    calc
      i (T (P f)) = U (i (P f)) := (hU (P f)).symm
      _ = U (Q (i f)) := congrArg U (hi_average ω Q hQ f)
      _ = Q' (U (i f)) := hUQ (i f)
      _ = Q' (i (T f)) := congrArg Q' (hU f)
      _ = i (P' (T f)) := (hi_average χ Q' hQ' (T f)).symm
  exact existsUnique_isotype_quotient_maps (X := S) (Y := E) P P' T Q Q' U i hTP hUQ hU

end CoarserTopology

-- Direct Lean invocations do not inherit the Lake option. The section-variable check
-- traverses the large instance terms in the transport and tensor proofs below.
set_option linter.unusedSectionVars false

section Transport

variable {A B : Type*} [CommGroup A] [TopologicalSpace A]
    [CommGroup B] [TopologicalSpace B]

/-- A topological group isomorphism restricts to a subgroup and its image. -/
private def continuousSubgroupMap (d : A ≃ₜ* B) (U : Subgroup A) :
    U ≃ₜ* U.map d.toMulEquiv.toMonoidHom where
  toMulEquiv := d.toMulEquiv.subgroupMap U
  continuous_toFun := (d.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (d.symm.continuous.comp continuous_subtype_val).subtype_mk _

variable [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A]
    [IsTopologicalGroup B] [T2Space B] [LocallyCompactSpace B]

/-- Transport of structural pairs preserves their open subgroups and good kernels. -/
private def transportBruhatPair (d : A ≃ₜ* B) (a : BruhatStructuralPair A) :
    BruhatStructuralPair B := by
  let U := a.val.1
  let N := OrderDual.ofDual a.val.2
  let D := d.toMulEquiv.toMonoidHom
  let φ := PontryaginDual.map (d.symm : B →ₜ* A)
  let ψ := PontryaginDual.map (d : A →ₜ* B)
  let δ : PontryaginDual A ≃ₜ* PontryaginDual B :=
    { φ with
      toFun := φ
      invFun := ψ
      left_inv := fun χ ↦ PontryaginDual.ext fun x ↦ by
        change χ (d.symm (d x)) = χ x
        rw [d.symm_apply_apply]
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ by
        change χ (d (d.symm x)) = χ x
        rw [d.apply_symm_apply]
      continuous_invFun := ψ.continuous }
  have hann : (lcaAnnihilator N).map δ.toMulEquiv.toMonoidHom = lcaAnnihilator (N.map D) := by
    ext χ
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, mem_lcaAnnihilator_iff,
      mem_lcaAnnihilator_iff]
    constructor
    · intro h x
      obtain ⟨y, hy, hxy⟩ := x.property
      calc
        χ (x : B) = χ (D y) := (congrArg χ hxy).symm
        _ = 1 := h ⟨y, hy⟩
    · intro h x
      exact h ⟨D x, Subgroup.mem_map_of_mem D x.property⟩
  refine ⟨(U.map D, OrderDual.toDual (N.map D)), ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact d.toHomeomorph.isOpenMap _ a.property.1
  · exact isCompactlyGeneratedGroup_of_continuousMulEquiv (continuousSubgroupMap d U)
      a.property.2.1
  · exact d.toHomeomorph.isClosedMap _ a.property.2.2.1.1
  · change IsOpen (lcaAnnihilator (N.map D) : Set (PontryaginDual B))
    rw [← hann]
    exact δ.toHomeomorph.isOpenMap _ a.property.2.2.1.2.1
  · change IsCompactlyGeneratedGroup (lcaAnnihilator (N.map D))
    rw [← hann]
    exact isCompactlyGeneratedGroup_of_continuousMulEquiv
      (continuousSubgroupMap δ (lcaAnnihilator N)) a.property.2.2.1.2.2
  · exact Subgroup.map_mono a.property.2.2.2

/-- Transport of pairs induces the corresponding isomorphism on their quotients. -/
private def transportBruhatQuotient (d : A ≃ₜ* B) (a : BruhatStructuralPair A) :
    a.quotient ≃ₜ* (transportBruhatPair d a).quotient := by
  let b := transportBruhatPair d a
  let dU : a.val.1 ≃ₜ* b.val.1 := continuousSubgroupMap d a.val.1
  let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
  let M := (OrderDual.ofDual b.val.2).comap b.val.1.subtype
  have hNM : N.map dU.toMulEquiv.toMonoidHom = M := by
    ext y
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap]
    change d.symm (y : B) ∈ OrderDual.ofDual a.val.2 ↔
      (y : B) ∈ (OrderDual.ofDual a.val.2).map d.toMulEquiv.toMonoidHom
    exact Subgroup.mem_map_equiv.symm
  let q := QuotientGroup.congr N M dU.toMulEquiv hNM
  exact
    { toMulEquiv := q
      continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp dU.continuous)
      continuous_invFun := isQuotientMap_quotient_mk'.continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp dU.symm.continuous) }

/-- The transported presentation uses the same elementary coordinates. -/
private abbrev transportBruhatPresentation (d : A ≃ₜ* B) (a : BruhatStructuralPair A)
    (e : ElementaryLCAPresentation a.quotient) :
    ElementaryLCAPresentation (transportBruhatPair d a).quotient :=
  { e with equiv := (transportBruhatQuotient d a).symm.trans e.equiv }

/-- Pushing a realized stage through a group isomorphism just changes its quotient
presentation, leaving its elementary Schwartz space unchanged. -/
private theorem transportBruhatStage (d : A ≃ₜ* B) (a : BruhatStructuralPair A)
    (e : ElementaryLCAPresentation a.quotient) :
    (LinearMap.funLeft ℂ ℂ d.symm).comp (schwartzBruhatStageRealization a e) =
      schwartzBruhatStageRealization (transportBruhatPair d a) (transportBruhatPresentation d a e) := by
  classical
  let b := transportBruhatPair d a
  let q := transportBruhatQuotient d a
  let e' := transportBruhatPresentation d a e
  refine LinearMap.ext fun s ↦ funext (d.surjective.forall.mpr ?_)
  intro x
  have hmem : d x ∈ b.val.1 ↔ x ∈ a.val.1 := by
    change d x ∈ a.val.1.map d.toMulEquiv.toMonoidHom ↔ _
    exact Subgroup.mem_map_iff_mem d.injective
  change schwartzBruhatStageRealization a e s (d.symm (d x)) =
    schwartzBruhatStageRealization b e' s (d x)
  rw [d.symm_apply_apply, schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ a.val.1
  · rw [dite_eq_left hx, dite_eq_left (hmem.mpr hx)]
    have hq : q (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨d x, hmem.mpr hx⟩ := rfl
    change s (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))) =
      s (Multiplicative.toAdd (e.equiv (q.symm (QuotientGroup.mk ⟨d x, hmem.mpr hx⟩))))
    rw [← hq, q.symm_apply_apply]
  · rw [dite_eq_right hx, dite_eq_right (hx ∘ hmem.mp)]

set_option maxHeartbeats 400000 in
/-- Pushing a function through a group isomorphism is continuous for the
Schwartz–Bruhat topology because it carries each stage into a stage. -/
private theorem schwartzBruhat_transport (d : A ≃ₜ* B) :
    ∃ T : SchwartzBruhat A →L[ℂ] SchwartzBruhat B,
      ∀ (f : SchwartzBruhat A) (y : B), T f y = f (d.symm y) := by
  let L := LinearMap.funLeft ℂ ℂ d.symm
  have hL : (schwartzBruhatSubmodule A).map L ≤ schwartzBruhatSubmodule B := by
    simp only [schwartzBruhatSubmodule, Submodule.map_iSup, iSup_le_iff]
    intro a e
    rintro w ⟨_, ⟨s, rfl⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem (transportBruhatPair d a)
      (Submodule.mem_iSup_of_mem (transportBruhatPresentation d a e)
        ⟨s, (LinearMap.congr_fun (transportBruhatStage d a e) s).symm⟩)
  let T : SchwartzBruhat A →ₗ[ℂ] SchwartzBruhat B :=
    (L.comp (schwartzBruhatSubmodule A).subtype).codRestrict (schwartzBruhatSubmodule B)
      (fun f ↦ hL ⟨f, f.property, rfl⟩)
  refine ⟨⟨T, ?_⟩, fun _ _ ↦ rfl⟩
  let pB : {p : Seminorm ℂ (schwartzBruhatSubmodule B) //
      ∀ (b : BruhatStructuralPair B) (e : ElementaryLCAPresentation b.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion b e)} →
          Seminorm ℂ (schwartzBruhatSubmodule B) := Subtype.val
  refine (withGeneratingSeminorms_spec _ pB).continuous_of_continuous_comp T fun p ↦ ?_
  let q := p.val.comp T
  have hq (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (q ∘ schwartzBruhatStageInclusion a e) := by
    let b := transportBruhatPair d a
    let e' := transportBruhatPresentation d a e
    have heq (s : SchwartzBruhatStage e) :
        schwartzBruhatStageInclusion b e' s = T (schwartzBruhatStageInclusion a e s) :=
      Subtype.ext (LinearMap.congr_fun (transportBruhatStage d a e) s).symm
    exact (p.property b e').congr fun s ↦ congrArg (fun f ↦ p.val f) (heq s)
  let i : {p : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} := ⟨q, hq⟩
  exact (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

/-- A topological group isomorphism transports Schwartz–Bruhat functions by
precomposition with its inverse. -/
private theorem schwartzBruhat_congr (d : A ≃ₜ* B) :
    ∃ T : SchwartzBruhat A ≃L[ℂ] SchwartzBruhat B,
      ∀ (f : SchwartzBruhat A) (x : A), T f (d x) = f x := by
  let T := (schwartzBruhat_transport d).choose
  have hT := (schwartzBruhat_transport d).choose_spec
  let U := (schwartzBruhat_transport d.symm).choose
  have hU := (schwartzBruhat_transport d.symm).choose_spec
  let E : SchwartzBruhat A ≃L[ℂ] SchwartzBruhat B :=
    { toLinearMap := T.toLinearMap
      invFun := U
      left_inv := fun f ↦ Subtype.ext (funext fun x ↦ calc
        U (T f) x = T f (d x) := hU (T f) x
        _ = f (d.symm (d x)) := hT f (d x)
        _ = f x := congrArg (fun a ↦ f a) (d.symm_apply_apply x))
      right_inv := fun f ↦ Subtype.ext (funext fun y ↦ calc
        T (U f) y = U f (d.symm y) := hT (U f) y
        _ = f (d (d.symm y)) := hU f (d.symm y)
        _ = f y := congrArg (fun b ↦ f b) (d.apply_symm_apply y))
      continuous_toFun := T.continuous
      continuous_invFun := U.continuous }
  refine ⟨E, fun f x ↦ ?_⟩
  change T f (d x) = f x
  exact (hT f (d x)).trans (congrArg (fun a ↦ f a) (d.symm_apply_apply x))

end Transport

section SplitModule

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local instance {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}
    (p : SeminormFamily ℂ X ι) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

/-- To intertwine an operator on a completed inductive tensor product with a continuous
linear map, it suffices to check their actions on pure tensors. -/
private theorem completion_inductiveTensor_intertwines
    {U V Z : Type*} [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ U] [PolynormableSpace ℂ V] [T2Space U] [T2Space V]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (A : U →L[ℂ] U) (B : V →L[ℂ] V) (C : Z →L[ℂ] Z)
    (e : Completion (InductiveTensor U V) ≃L[ℂ] Z)
    (h : ∀ f g, e (Completion.coe' (α := InductiveTensor U V) (A f ⊗ₜ[ℂ] B g)) =
      C (e (Completion.coe' (α := InductiveTensor U V) (f ⊗ₜ[ℂ] g))))
    (z : Completion (InductiveTensor U V)) :
    e (Completion.map (inductiveTensorMap A.toLinearMap B.toLinearMap :
      InductiveTensor U V → InductiveTensor U V) z) = C (e z) := by
  let M := inductiveTensorMap A.toLinearMap B.toLinearMap
  let j : InductiveTensor U V →L[ℂ] Completion (InductiveTensor U V) := Completion.toComplL
  let F : U ⊗[ℂ] V →ₗ[ℂ] Z := e.toLinearEquiv.toLinearMap.comp j.toLinearMap
  have hlin : F.comp (TensorProduct.map A.toLinearMap B.toLinearMap) = C.toLinearMap.comp F :=
    TensorProduct.ext' h
  have hM : UniformContinuous (M : InductiveTensor U V → InductiveTensor U V) :=
    uniformContinuous_addMonoidHom_of_continuous (inductiveTensorMap_continuous A B)
  exact Completion.ext' (e.continuous.comp Completion.continuous_map)
    (C.continuous.comp e.continuous) (fun w ↦
      (congrArg (fun y ↦ e y) (Completion.map_coe hM w)).trans (LinearMap.congr_fun hlin w)) z

section TensorTranslation

variable {X Y G : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]

local notation "HS" => InductiveTensor (SchwartzBruhat X) (SchwartzBruhat Y)
local notation "S" => SchwartzBruhat G

/-- Point evaluations separate Schwartz–Bruhat functions. -/
theorem schwartzBruhat_eval_t2 {A : Type*} [CommGroup A] [TopologicalSpace A] :
    T2Space (SchwartzBruhat A) :=
  T2Space.of_injective_continuous
    (f := fun f : SchwartzBruhat A ↦ (f : A → ℂ)) (fun _ _ h ↦ Subtype.ext h)
    (continuous_pi continuous_schwartzBruhat_eval)

/-- If a tensor isomorphism multiplies evaluations in product coordinates, it
intertwines left translation on the completion. -/
private theorem schwartzBruhat_tensor_intertwines
    (d : X × Y ≃ₜ* G) (e : Completion HS ≃L[ℂ] S)
    (he : ∀ (f : SchwartzBruhat X) (h : SchwartzBruhat Y) (k : X) (t : Y),
        e (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h)) (d (k, t)) = f k * h t)
    (k : X) (t : Y) (z : Completion HS) :
    e (Completion.map (inductiveTensorMap
      ((schwartzBruhatTranslationAction (G := X)) k).toLinearMap
      ((schwartzBruhatTranslationAction (G := Y)) t).toLinearMap : HS → HS) z) =
    schwartzBruhatTranslate (d (k, t)) (e z) := by
  have : T2Space (SchwartzBruhat X) := schwartzBruhat_eval_t2
  have : T2Space (SchwartzBruhat Y) := schwartzBruhat_eval_t2
  have : T2Space S := schwartzBruhat_eval_t2
  refine (completion_inductiveTensor_intertwines (schwartzBruhatTranslationAction (G := X) k)
    (schwartzBruhatTranslationAction (G := Y) t)
    (schwartzBruhatTranslationAction (G := G) (d (k, t))) e ?_ z).trans ?_
  · intro f h
    refine Subtype.ext (funext (d.surjective.forall.mpr ?_))
    rintro ⟨a, b⟩
    have hshift : (d (k, t))⁻¹ * d (a, b) = d (k⁻¹ * a, t⁻¹ * b) :=
      ((map_mul d (k, t)⁻¹ (a, b)).trans
        (congrArg (· * d (a, b)) (map_inv d (k, t)))).symm
    have lhs := he (schwartzBruhatTranslationAction (G := X) k f)
      (schwartzBruhatTranslationAction (G := Y) t h) a b
    have rhs := schwartzBruhatTranslationAction_apply (d (k, t)) (d (a, b))
      (e (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h)))
    calc
      _ = _ := lhs
      _ = f (k⁻¹ * a) * h (t⁻¹ * b) := congrArg₂ (· * ·)
        (schwartzBruhatTranslationAction_apply k a f) (schwartzBruhatTranslationAction_apply t b h)
      _ = _ := (he f h (k⁻¹ * a) (t⁻¹ * b)).symm
      _ = _ := congrArg (fun x : G ↦ e (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h)) x) hshift.symm
      _ = _ := rhs.symm
  · exact Subtype.ext (funext fun x ↦ schwartzBruhatTranslationAction_apply (d (k, t)) x (e z))

end TensorTranslation

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)

local notation "K" => m.toMonoidHom.ker
local notation "Γ" => m.toMonoidHom.range
local notation "S" => SchwartzBruhat G
local notation "SΓ" => SchwartzBruhat Γ
local notation "SK" => SchwartzBruhat K
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
        schwartzBruhatTranslate ((k : G) * τ t) (e z) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology ℝ≥0ˣ :=
    (Units.isEmbedding_val₀ (G₀ := ℝ≥0)).secondCountableTopology
  let : SecondCountableTopology Γ := TopologicalSpace.Subtype.secondCountableTopology (Γ : Set ℝ≥0ˣ)
  let : LocallyCompactSpace Γ := hm.isClosed_range.locallyCompactSpace
  refine (hm.exists_prod_equiv τ hτ).elim fun d hd ↦ ?_
  have hKernel : ∃ P : Completion HS ≃L[ℂ] SchwartzBruhat (K × Γ),
      ∀ (f : SK) (h : SΓ) (k : K) (t : Γ),
        P (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h)) (k, t) = f k * h t := by
    with_reducible exact schwartzBruhat_kernel_equiv (G := K) (H := Γ)
  obtain ⟨P, hP⟩ := hKernel
  refine (schwartzBruhat_congr d).elim fun T hT ↦ ?_
  let e := P.trans T
  have he (f : SchwartzBruhat K) (h : SΓ) (k : K) (t : Γ) :
      e (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h)) (d (k, t)) = f k * h t := by
    change T (P (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h))) (d (k, t)) = _
    with_reducible exact (hT _ (k, t)).trans (hP f h k t)
  clear_value e
  refine ⟨e, ?_, ?_⟩
  · intro f h k t
    exact Eq.subst (motive := fun x : G ↦
      e (Completion.coe' (α := HS) (f ⊗ₜ[ℂ] h)) x = f k * h t) (hd k t) (he f h k t)
  · intro k t z
    calc
      _ = schwartzBruhatTranslate (d (k, t)) (e z) := by
        with_reducible_and_instances
          exact schwartzBruhat_tensor_intertwines (X := K) (Y := Γ) d e he k t z
      _ = _ := congrArg (fun g : G ↦ schwartzBruhatTranslate g (e z)) (hd k t)

omit hm in
/-- The constant function one is a Schwartz–Bruhat function on a compact group. -/
theorem compact_schwartzBruhat_one {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [CompactSpace H] :
    ∃ c : SchwartzBruhat H, ∀ k, c k = 1 := by
  have hcompact : IsCompact ((⊤ : Subgroup H) : Set H) := isCompact_univ
  have : CompactSpace (⊤ : Subgroup H) := isCompact_iff_compactSpace.mp hcompact
  have : CompactSpace (lcaAnnihilator (⊤ : Subgroup H)) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator ⊤ isOpen_univ)
  let a : BruhatStructuralPair H :=
    ⟨(⊤, OrderDual.toDual ⊤), isOpen_univ,
      isCompactlyGeneratedGroup_of_compact (G := (⊤ : Subgroup H)),
      ⟨isClosed_univ, isOpen_lcaAnnihilator ⊤ hcompact,
        isCompactlyGeneratedGroup_of_compact (G := lcaAnnihilator (⊤ : Subgroup H))⟩, le_rfl⟩
  have : Subsingleton a.quotient := by
    change Subsingleton ((⊤ : Subgroup H) ⧸ (⊤ : Subgroup (⊤ : Subgroup H)))
    exact QuotientGroup.subsingleton_quotient_top
  let A := Multiplicative (ElementaryLieGroup 0 0 0 PUnit)
  have : Subsingleton A := by
    change Subsingleton (ElementaryLieGroup 0 0 0 PUnit)
    infer_instance
  let f : a.quotient →* A := 1
  let e₀ : a.quotient ≃* A := MulEquiv.ofBijective f
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨1, Subsingleton.elim _ y⟩⟩
  let e : ElementaryLCAPresentation a.quotient :=
    { realDim := 0
      torusDim := 0
      latticeRank := 0
      finiteFactor := PUnit
      equiv := { e₀ with
        continuous_toFun := (continuous_const (y := (1 : A))).congr fun _ ↦ Subsingleton.elim _ _
        continuous_invFun := (continuous_const (y := (1 : a.quotient))).congr
          fun _ ↦ Subsingleton.elim _ _ } }
  let s : SchwartzBruhatStage e := ⟨fun _ ↦ 1, by
    refine ⟨fun _ _ ↦ contDiff_const, ?_⟩
    intro idx
    have hi : idx = (0, 0, 0, 0) := Subsingleton.elim _ _
    subst idx
    simp [elementarySchwartzBound_zero]⟩
  refine ⟨schwartzBruhatStageInclusion a e s, fun k ↦ ?_⟩
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (show k ∈ a.val.1 from Subgroup.mem_top k)]

omit hm in
/-- Contracting the first tensor factor by a continuous functional gives a map to the
complete second factor. Its scalar evaluations are determined on pure tensors. -/
theorem exists_tensor_restriction {U V W ι : Type*}
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [PolynormableSpace ℂ U] [T2Space U]
    [AddCommGroup V] [Module ℂ V] [UniformSpace V] [IsUniformAddGroup V]
    [PolynormableSpace ℂ V] [T2Space V] [ContinuousSMul ℂ V] [CompleteSpace V]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (φ : U →L[ℂ] ℂ) (ev : ι → V →L[ℂ] ℂ) (res : ι → W →L[ℂ] ℂ)
    (e : Completion (InductiveTensor U V) ≃L[ℂ] W)
    (h : ∀ u v i, res i (e (Completion.coe' (α := InductiveTensor U V) (u ⊗ₜ[ℂ] v))) =
      φ u * ev i v) :
    ∃ r : W →L[ℂ] V, ∀ w i, ev i (r w) = res i w := by
  let L : InductiveTensor U V →ₗ[ℂ] V :=
    TensorProduct.lift ((LinearMap.lsmul ℂ V).comp φ.toLinearMap)
  let T : InductiveTensor U V →L[ℂ] V :=
    ⟨L, (continuous_inductiveTensor_iff L).2
      ⟨fun u ↦ continuous_id.const_smul (φ u), fun v ↦ φ.continuous.smul (continuous_const (y := v))⟩⟩
  refine ⟨T.fromCompletion.comp e.symm.toContinuousLinearMap, fun w i ↦ ?_⟩
  let A := (ev i).comp T.fromCompletion
  let B := (res i).comp e.toContinuousLinearMap
  let j : InductiveTensor U V →L[ℂ] Completion (InductiveTensor U V) := Completion.toComplL
  have hAB : (A.comp j).toLinearMap = (B.comp j).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    calc
      _ = ev i (T (u ⊗ₜ[ℂ] v)) := congrArg (ev i) (T.fromCompletion_apply_coe (u ⊗ₜ[ℂ] v))
      _ = φ u * ev i v := (ev i).map_smul (φ u) v
      _ = _ := (h u v i).symm
  have hEq := Completion.ext' A.continuous B.continuous (LinearMap.congr_fun hAB) (e.symm w)
  exact hEq.trans (congrArg (res i) (e.apply_symm_apply w))

omit hm in
/-- Point evaluation as a continuous linear functional on Schwartz–Bruhat functions. -/
private abbrev schwartzBruhatEvalCLM {A : Type*} [CommGroup A] [TopologicalSpace A] (x : A) :
    SchwartzBruhat A →L[ℂ] ℂ :=
  { toFun := fun f ↦ f x
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    cont := continuous_schwartzBruhat_eval x }

/-- Restriction to the splitting section sends Schwartz–Bruhat functions to
Schwartz–Bruhat functions on the image of the module and is continuous linear. -/
theorem schwartzBruhat_modulation_section_restriction (τ : Γ →ₜ* G)
    (hτ : ∀ t, m (τ t) = (t : ℝ≥0ˣ)) :
    ∃ r : S →L[ℂ] SΓ, ∀ (f : S) (t : Γ), r f t = f (τ t) := by
  have hTensor := @schwartzBruhat_modulation_tensor G _ _ _ _ _ _ m hm τ hτ
  rcases hTensor with ⟨e, he, _⟩
  let : LocallyCompactSpace Γ := hm.isClosed_range.locallyCompactSpace
  let : T2Space SK := schwartzBruhat_eval_t2 (A := K)
  let : T2Space SΓ := schwartzBruhat_eval_t2 (A := Γ)
  let : CompleteSpace SΓ := schwartzBruhat_complete (G := Γ)
  with_reducible_and_instances
    refine exists_tensor_restriction (U := SK) (V := SΓ) (W := S) (ι := Γ)
      (schwartzBruhatEvalCLM (1 : K)) (fun t ↦ schwartzBruhatEvalCLM t)
      (fun t ↦ schwartzBruhatEvalCLM (τ t)) e ?_
  intro u v t
  let F : G → ℂ := e (Completion.coe' (α := HS) (u ⊗ₜ[ℂ] v))
  have h : F ((1 : G) * τ t) = u 1 * v t := he u v 1 t
  with_reducible_and_instances change F (τ t) = u 1 * v t
  clear_value F
  exact (congrArg F (one_mul (τ t))).symm.trans h

set_option linter.unusedSectionVars false in
/-- The tensor isomorphism gives pullback of profiles and restriction to the section. -/
private theorem schwartzBruhat_modulation_profile_maps (τ : Γ →ₜ* G)
    (hτ : ∀ t, m (τ t) = (t : ℝ≥0ˣ)) :
    ∃ (j : SΓ →L[ℂ] S) (r : S →L[ℂ] SΓ),
      (∀ (f : SΓ) (k : K) (t : Γ), j f ((k : G) * τ t) = f t) ∧
      ∀ (f : S) (t : Γ), r f t = f (τ t) := by
  let hcompact : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology ℝ≥0ˣ :=
    (Units.isEmbedding_val₀ (G₀ := ℝ≥0)).secondCountableTopology
  let : SecondCountableTopology Γ := TopologicalSpace.Subtype.secondCountableTopology (Γ : Set ℝ≥0ˣ)
  let : LocallyCompactSpace Γ := hm.isClosed_range.locallyCompactSpace
  let : T2Space SK := schwartzBruhat_t2
  let : T2Space SΓ := schwartzBruhat_t2
  let hloc : LocallyCompactSpace K := hm.isCompact_ker.isClosed.locallyCompactSpace
  have hc' : ∃ c : SK, ∀ k : K, c k = 1 := by
    with_reducible
      exact @compact_schwartzBruhat_one K inferInstance inferInstance inferInstance inferInstance
        hloc hcompact
  obtain ⟨c, hc⟩ := hc'
  have hTensor := @schwartzBruhat_modulation_tensor G ‹CommGroup G› ‹TopologicalSpace G›
    ‹IsTopologicalGroup G› ‹T2Space G› ‹LocallyCompactSpace G› ‹SecondCountableTopology G› m hm τ hτ
  rcases hTensor with ⟨e, he, _⟩
  let J : SΓ →L[ℂ] HS :=
    ⟨TensorProduct.mk ℂ SK SΓ c, by
      exact ((continuous_inductiveTensor_iff (LinearMap.id : HS →ₗ[ℂ] HS)).1 continuous_id).1 c⟩
  let emb : HS →L[ℂ] Completion HS := by
    with_reducible exact @Completion.toComplL HS ℂ _ _ _ _ _ _
  let j : SΓ →L[ℂ] S := by
    with_reducible exact e.toContinuousLinearMap.comp (emb.comp J)
  have hRestriction := @schwartzBruhat_modulation_section_restriction G
    ‹CommGroup G› ‹TopologicalSpace G› ‹IsTopologicalGroup G› ‹T2Space G›
    ‹LocallyCompactSpace G› ‹SecondCountableTopology G› m hm τ hτ
  rcases hRestriction with ⟨r, hr⟩
  refine ⟨j, r, ?_, hr⟩
  · intro f k t
    have hJ : J f = c ⊗ₜ[ℂ] f := rfl
    with_reducible
      simpa only [j, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, emb,
        Completion.coe_toComplL, hJ, hc k, one_mul] using he c f k t

omit hm in
/-- Profiles that parametrize the projection of a dense subspace give a dense
embedding into the complete kernel quotient. -/
private theorem isotype_completion_of_projected_profiles {X Y E : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [T2Space E] [CompleteSpace E] (Q : E →L[ℂ] E) (hQQ : ∀ u, Q (Q u) = Q u)
    (i : Y →L[ℂ] E) (hi : Injective i) (hd : DenseRange i)
    (j w : X →L[ℂ] Y) (hw : Injective w) (hFix : ∀ f, Q (i (w f)) = i (w f))
    (hSurj : ∀ f : Y, ∃ g : X, i (w g) = Q (i f))
    (M N : Y →L[ℂ] Y)
    (hM : @Continuous Y E (TopologicalSpace.induced i inferInstance) _ (fun f ↦ i (M f)))
    (hN : @Continuous Y E (TopologicalSpace.induced i inferInstance) _ (fun f ↦ i (N f)))
    (hW : ∀ f, M (j f) = w f) (hJ : ∀ f, N (w f) = j f) :
    let q := Q.ker.mkQL.comp (i.comp w)
    Injective q ∧ DenseRange q ∧
      TopologicalSpace.induced (fun f ↦ i (j f)) inferInstance =
        TopologicalSpace.induced q inferInstance ∧
      @CompleteSpace (E ⧸ Q.ker) (IsTopologicalAddGroup.rightUniformSpace _) := by
  have hInduced (L : Y →L[ℂ] Y)
      (hL : @Continuous Y E (TopologicalSpace.induced i inferInstance) _
        (fun f ↦ i (L f))) (l : X →L[ℂ] Y) :
      TopologicalSpace.induced (fun f ↦ i (l f)) inferInstance ≤
        TopologicalSpace.induced (fun f ↦ i (L (l f))) inferInstance := by
    have hle : TopologicalSpace.induced i (inferInstance : TopologicalSpace E) ≤
        TopologicalSpace.induced (fun f ↦ i (L f)) inferInstance :=
      @Continuous.le_induced Y E (TopologicalSpace.induced i inferInstance) _
        (fun f ↦ i (L f)) hL
    calc
      _ = TopologicalSpace.induced l (TopologicalSpace.induced i inferInstance) :=
        induced_compose.symm
      _ ≤ TopologicalSpace.induced l
          (TopologicalSpace.induced (fun f ↦ i (L f)) inferInstance) :=
        induced_mono hle
      _ = _ := induced_compose
  have hTop : TopologicalSpace.induced (fun f ↦ i (j f)) inferInstance =
      TopologicalSpace.induced (fun f ↦ i (w f)) inferInstance := by
    apply le_antisymm
    · simpa only [hW] using hInduced M hM j
    · simpa only [hJ] using hInduced N hN w
  let q := Q.ker.mkQL.comp (i.comp w)
  let F : (E ⧸ Q.ker) →L[ℂ] E := Q.ker.liftQL Q le_rfl
  have hleft : LeftInverse Q.ker.mkQL F := by
    intro z
    obtain ⟨u, rfl⟩ := Q.ker.mkQ_surjective z
    change Q.ker.mkQ (Q u) = Q.ker.mkQ u
    apply (Submodule.Quotient.eq Q.ker).2
    change Q (Q u - u) = 0
    rw [map_sub, hQQ, sub_self]
  have hF : IsInducing F :=
    (hleft.isEmbedding Q.ker.mkQL.continuous F.continuous).isInducing
  have hFq (f : X) : F (q f) = i (w f) := hFix f
  change Injective q ∧ DenseRange q ∧ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g hfg
    exact hw (hi ((hFq f).symm.trans ((congrArg F hfg).trans (hFq g))))
  · have hdq : DenseRange (Q.ker.mkQL ∘ i) :=
      Q.ker.mkQ_surjective.denseRange.comp hd Q.ker.mkQL.continuous
    refine Dense.mono ?_ hdq
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hSurj f
    refine ⟨g, ?_⟩
    change Q.ker.mkQL (i (w g)) = Q.ker.mkQL (i f)
    rw [hg]
    exact hleft (Q.ker.mkQ (i f))
  · calc
      _ = TopologicalSpace.induced (fun f ↦ i (w f)) inferInstance := hTop
      _ = TopologicalSpace.induced ((F : (E ⧸ Q.ker) → E) ∘ q) inferInstance :=
        congrArg (fun g : X → E ↦ TopologicalSpace.induced g inferInstance) (funext hFq).symm
      _ = _ := induced_compose.symm.trans
        (congrArg (TopologicalSpace.induced (q : X → E ⧸ Q.ker)) hF.eq_induced.symm)
  · let : UniformSpace (E ⧸ Q.ker) := IsTopologicalAddGroup.rightUniformSpace _
    have : IsUniformAddGroup (E ⧸ Q.ker) := isUniformAddGroup_of_addCommGroup
    apply (completeSpace_iff_isComplete_range
      (AddMonoidHom.isUniformInducing_of_isInducing (f := F) hF)).2
    have hRange : range F = {u | Q u = u} := by
      ext u
      constructor
      · rintro ⟨z, rfl⟩
        obtain ⟨v, rfl⟩ := Q.ker.mkQ_surjective z
        exact hQQ v
      · intro hu
        exact ⟨Q.ker.mkQ u, hu⟩
    rw [hRange]
    exact (isClosed_eq Q.continuous continuous_id).isComplete


omit hm in
set_option linter.unusedSectionVars false in
/-- The weighted profile functions are precisely the isotypic Schwartz–Bruhat functions. -/
private theorem schwartzBruhat_modulation_weighted_profiles
    (τ : Γ →ₜ* G) (ω : PontryaginDual K)
    (e : (K × Γ) ≃ₜ* G) (he : ∀ (k : K) (t : Γ), e (k, t) = (k : G) * τ t)
    (w : SΓ →L[ℂ] S) (r : S →L[ℂ] SΓ)
    (hw : ∀ (f : SΓ) (k : K) (t : Γ), w f ((k : G) * τ t) = star (ω k : ℂ) * f t)
    (hr : ∀ (f : S) (t : Γ), r f t = f (τ t)) :
    (∀ f : SΓ, w f ∈ actionIsotype
      ((schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)) ω) ∧
      (∀ f : S, f ∈ actionIsotype
        ((schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)) ω →
        w (r f) = f) := by
  let ρS := (schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)
  have hCoordinates (x : G) : ∃ (k : K) (t : Γ), x = (k : G) * τ t := by
    have hx := e.surjective x
    rcases hx with ⟨⟨k, t⟩, h⟩
    exact ⟨k, t, h.symm.trans (he k t)⟩
  have hSmul (c : ℂ) (f : S) (x : G) : (c • f : S) x = c * f x := rfl
  have hAction (k : K) (f : S) :
      ρS k f = schwartzBruhatTranslationAction (G := G) (k : G) f := rfl
  have hCharacter (l k : K) :
      star (ω (l⁻¹ * k) : ℂ) = (ω l : ℂ) * star (ω k : ℂ) := by
    calc
      _ = (ω ((l⁻¹ * k)⁻¹) : ℂ) := by rw [map_inv, Circle.coe_inv_eq_conj, starRingEnd_apply]
      _ = _ := by
        rw [mul_inv_rev, inv_inv, map_mul, Circle.coe_mul, map_inv,
          Circle.coe_inv_eq_conj, starRingEnd_apply, mul_comm]
  have hwMem (f : SΓ) : w f ∈ actionIsotype ρS ω := by
    apply (mem_actionIsotype ρS ω (w f)).2
    intro l
    refine Subtype.ext (funext fun x ↦ ?_)
    have hx := hCoordinates x
    rcases hx with ⟨k, t, hx⟩
    have hShift : (l : G)⁻¹ * x = ((l⁻¹ * k : K) : G) * τ t := by
      rw [hx, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    have hEval : w f ((l : G)⁻¹ * x) = (ω l : ℂ) * w f x := calc
      _ = w f (((l⁻¹ * k : K) : G) * τ t) := congrArg (fun u : G ↦ w f u) hShift
      _ = star (ω (l⁻¹ * k) : ℂ) * f t := hw f (l⁻¹ * k) t
      _ = (ω l : ℂ) * (star (ω k : ℂ) * f t) := by rw [hCharacter, mul_assoc]
      _ = _ := congrArg ((ω l : ℂ) * ·) ((congrArg (fun u : G ↦ w f u) hx).trans (hw f k t)).symm
    have hTranslate := schwartzBruhatTranslationAction_apply (G := G) (l : G) x (w f)
    exact (congrArg (fun g : S ↦ g x) (hAction l (w f))).trans
      (hTranslate.trans (hEval.trans (hSmul (ω l : ℂ) (w f) x).symm))
  have hwSurj (f : S) (hf : f ∈ actionIsotype ρS ω) : w (r f) = f := by
    refine Subtype.ext (funext fun x ↦ ?_)
    have hx := hCoordinates x
    rcases hx with ⟨k, t, hx⟩
    have hIso := (mem_actionIsotype ρS ω f).1 hf k⁻¹
    have h := congrArg (fun g : S ↦ g (τ t)) ((hAction k⁻¹ f).symm.trans hIso)
    have hTranslate := schwartzBruhatTranslationAction_apply (G := G) (↑(k⁻¹) : G) (τ t) f
    have hEval := hTranslate.symm.trans (h.trans (hSmul (ω k⁻¹ : ℂ) f (τ t)))
    rw [Subgroup.coe_inv, inv_inv, map_inv, Circle.coe_inv_eq_conj, starRingEnd_apply] at hEval
    with_reducible
      exact (congrArg (fun u : G ↦ w (r f) u) hx).trans
        ((hw (r f) k t).trans ((congrArg (star (ω k : ℂ) * ·) (hr f t)).trans
          (hEval.symm.trans (congrArg (fun u : G ↦ f u) hx).symm)))
  exact ⟨hwMem, hwSurj⟩

/-- The source projector has the normalized Pettis formula and takes values in the isotype. -/
private theorem schwartzBruhat_modulation_source_projector
    [MeasurableSpace G] [BorelSpace G] (μ₁ : Measure K) [hμ₁ : μ₁.IsHaarMeasure]
    (ω : PontryaginDual K) :
    let ρS := (schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)
    let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
    IsPettisIsotypicAverageOn μ₁ univ ρS ω (μ₁.real univ • P) ∧
      (∀ f : S, P f ∈ actionIsotype ρS ω) ∧
      (∀ f : S, f ∈ actionIsotype ρS ω → P f = f) := by
  intro ρS P
  have hQuotient : ∃ p : (S ⧸ P.ker) ≃L[ℂ] actionIsotype ρS ω,
      ∀ f : S, (p (P.ker.mkQ f) : S) = P f := by
    with_reducible exact schwartzBruhatIsotypicProjector_quotient_equiv m hm μ₁ ω
  obtain ⟨p, hp⟩ := hQuotient
  have hPmem (f : S) : P f ∈ actionIsotype ρS ω := by
    exact Eq.mp (congrArg (fun u : S ↦ u ∈ actionIsotype ρS ω) (hp f))
      (p (P.ker.mkQ f)).property
  have hSourceAverage := @exists_schwartzBruhatIsotypicProjector_average G
    ‹CommGroup G› ‹TopologicalSpace G› ‹IsTopologicalGroup G› ‹T2Space G›
    ‹LocallyCompactSpace G› ‹SecondCountableTopology G› ‹MeasurableSpace G› ‹BorelSpace G›
    m hm μ₁ hμ₁ ω
  rcases hSourceAverage with ⟨P', hP', hPavg'⟩
  have hPavg : IsPettisIsotypicAverageOn μ₁ univ ρS ω (μ₁.real univ • P) := by
    have hUnique := existsUnique_schwartzBruhatIsotypicProjector m hm μ₁ ω
    have hP'P : P' = P := hUnique.unique hP' (Classical.choose_spec hUnique.exists)
    exact hP'P ▸ hPavg'
  have hPfix := @schwartzBruhatIsotypicProjector_apply_isotype G
    ‹CommGroup G› ‹TopologicalSpace G› ‹IsTopologicalGroup G› ‹T2Space G›
    ‹LocallyCompactSpace G› ‹SecondCountableTopology G› ‹MeasurableSpace G› ‹BorelSpace G›
    m hm μ₁ hμ₁ ω
  exact ⟨hPavg, hPmem, hPfix⟩

omit hm in
/-- Isotypic averages commute with a continuous equivariant linear map. -/
private theorem isotype_average_commutes {H X Y : Type*}
    [Monoid H] [TopologicalSpace H] [MeasurableSpace H]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [SeparatingDual ℂ Y]
    (μ : Measure H) (ω : PontryaginDual H)
    (σ : H →* (X →L[ℂ] X)) (ρ : H →* (Y →L[ℂ] Y))
    (P : X →L[ℂ] X) (Q : Y →L[ℂ] Y)
    (hP : IsPettisIsotypicAverageOn μ univ σ ω P)
    (hQ : IsPettisIsotypicAverageOn μ univ ρ ω Q)
    (i : X →L[ℂ] Y) (hi : ∀ k f, i (σ k f) = ρ k (i f)) (f : X) :
    Q (i f) = i (P f) := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro φ
  rw [pettisIntegral_univ_eval (hQ (i f)) φ]
  have h := pettisIntegral_univ_eval (hP f) (φ.comp i)
  change φ (i (P f)) =
    ∫ k : H, φ (i (star (ω k : ℂ) • σ k f)) ∂μ at h
  rw [h]
  apply integral_congr_ae (ae_of_all _ fun k ↦ ?_)
  rw [i.map_smul, hi]

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [hE : CompleteSpace E]
  [MeasurableSpace G] [BorelSpace G]
  (μ₁ : Measure m.toMonoidHom.ker) [hμ₁ : μ₁.IsHaarMeasure]
  (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
  (i : SchwartzBruhat G →L[ℂ] E) (hi : Injective i) (hd : DenseRange i)
  (hcomm : ∀ (g : G) (f : SchwartzBruhat G),
    i (schwartzBruhatTranslationAction (G := G) g f) = ρ g (i f))

include hE hμ₁ hρ hi hd hcomm

set_option linter.unusedSectionVars false in
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
          TopologicalSpace.induced q inferInstance ∧ @CompleteSpace (E ⧸ Q.ker) (IsTopologicalAddGroup.rightUniformSpace _) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let ρE := ρ.comp (Subgroup.subtype K)
  let ρS := (schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)
  have hρK : Continuous (fun p : K × E ↦ ρE p.1 p.2) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hseqK (u : ℕ → E) (v : E) (hu : Tendsto u atTop (𝓝 v)) :
      TendstoUniformly (fun n k ↦ ρE k (u n)) (fun k ↦ ρE k v) atTop := by
    intro V hV
    filter_upwards [hseq u v hu V hV] with n hn k
    exact hn (k : G)
  let : LocallyCompactSpace K := hm.isCompact_ker.isClosed.locallyCompactSpace
  have hAvg : ∃! A : E →L[ℂ] E, IsPettisIsotypicAverageOn μ₁ univ ρE ω A := by
    with_reducible
      exact existsUnique_compactActionIsotypicAverage (G := K) (E := E) μ₁ ρE hρK hborn hseqK ω
  obtain ⟨A, hA, _⟩ := hAvg
  let Q : E →L[ℂ] E := (μ₁.real univ)⁻¹ • A
  have hmass : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  have hQ : IsPettisIsotypicAverageOn μ₁ univ ρE ω (μ₁.real univ • Q) := by
    simpa only [Q, smul_inv_smul₀ hmass] using hA
  have hIdempotent : Q.comp Q = Q := by
    with_reducible
      exact compactActionAverage_idempotent (G := K) (E := E) μ₁ ρE hρK ω A hA
  have hQQ (u : E) : Q (Q u) = Q u := DFunLike.congr_fun hIdempotent u
  have hProfiles : ∃ (j : SΓ →L[ℂ] S) (r : S →L[ℂ] SΓ),
      (∀ (f : SΓ) (k : K) (t : Γ), j f ((k : G) * τ t) = f t) ∧
      ∀ (f : S) (t : Γ), r f t = f (τ t) := by
    with_reducible exact schwartzBruhat_modulation_profile_maps (G := G) m hm τ hτ
  obtain ⟨j, r, hj, hr⟩ := hProfiles
  have hSplit : ∃ e : (K × Γ) ≃ₜ* G, ∀ (k : K) (t : Γ), e (k, t) = (k : G) * τ t := by
    with_reducible
      exact @IsModulation.exists_prod_equiv G ‹CommGroup G› ‹TopologicalSpace G›
        ‹IsTopologicalGroup G› ‹T2Space G› ‹LocallyCompactSpace G› ‹SecondCountableTopology G›
        m hm τ hτ
  obtain ⟨e, he⟩ := hSplit
  let πK : G →ₜ* K := (ContinuousMonoidHom.fst K Γ).comp
    (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  let χ : PontryaginDual G := PontryaginDual.map πK ω⁻¹
  have hχ (k : K) (t : Γ) : (χ ((k : G) * τ t) : ℂ) = star (ω k : ℂ) := by
    have hπ : πK ((k : G) * τ t) = k := by
      rw [← he k t]
      exact congrArg Prod.fst (e.symm_apply_apply (k, t))
    change (ω⁻¹ (πK ((k : G) * τ t)) : ℂ) = _
    rw [hπ]
    exact Circle.coe_inv_eq_conj (ω k)
  have hMul := hmul χ
  have hMulInv := hmul (χ⁻¹ : PontryaginDual G)
  rcases hMul with ⟨M, hM, hMcont⟩
  rcases hMulInv with ⟨N, hN, hNcont⟩
  have hNM (f : S) : N (M f) = f := by
    apply Subtype.ext
    funext x
    change N (M f) x = f x
    rw [hN, hM, ← mul_assoc]
    change (↑((χ x)⁻¹) : ℂ) * (χ x : ℂ) * f x = f x
    rw [Circle.coe_inv, inv_mul_cancel₀ (Circle.coe_ne_zero (χ x)), one_mul]
  let w : SΓ →L[ℂ] S := M.comp j
  have hw (f : SΓ) (k : K) (t : Γ) :
      w f ((k : G) * τ t) = star (ω k : ℂ) * f t := by
    change M (j f) ((k : G) * τ t) = _
    rw [hM, hj, hχ]
  refine ⟨Q, j, w, hQ, fun f k t ↦ ⟨hj f k t, hw f k t⟩, ?_⟩
  have hWeighted : (∀ f : SΓ, w f ∈ actionIsotype ρS ω) ∧
      (∀ f : S, f ∈ actionIsotype ρS ω → w (r f) = f) := by
    with_reducible
      exact schwartzBruhat_modulation_weighted_profiles (G := G) m τ ω e he w r hw hr
  obtain ⟨hwMem, hwSurj⟩ := hWeighted
  let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
  have hSource : IsPettisIsotypicAverageOn μ₁ univ ρS ω (μ₁.real univ • P) ∧
      (∀ f : S, P f ∈ actionIsotype ρS ω) ∧
      (∀ f : S, f ∈ actionIsotype ρS ω → P f = f) := by
    with_reducible
      exact schwartzBruhat_modulation_source_projector (G := G) m hm μ₁ ω
  obtain ⟨hPavg, hPmem, hPfix⟩ := hSource
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  have hCommK (k : K) (g : S) : i (ρS k g) = ρE k (i g) := hcomm (k : G) g
  have hQP (f : S) : Q (i f) = i (P f) := by
    have hAcomp : (μ₁.real univ • Q) (i f) = i ((μ₁.real univ • P) f) := by
      with_reducible
        exact isotype_average_commutes (H := K) (X := S) (Y := E) μ₁ ω ρS ρE _ _ hPavg hQ i
          hCommK f
    exact smul_right_injective E hmass (hAcomp.trans (i.map_smul_of_tower (μ₁.real univ) (P f)))
  have hfix (f : SΓ) : Q (i (w f)) = i (w f) :=
    (hQP (w f)).trans (congrArg i (hPfix (w f) (hwMem f)))
  have hwInj : Injective w := by
    intro f g hfg
    apply Subtype.ext
    funext t
    have ht := congrArg (fun v : S ↦ v ((1 : K) * τ t)) hfg
    simpa only [hw f 1 t, hw g 1 t, map_one, Circle.coe_one, star_one, one_mul] using ht
  have hSurj (f : S) : ∃ g : SΓ, i (w g) = Q (i f) :=
    ⟨r (P f), (congrArg i (hwSurj (P f) (hPmem f))).trans (hQP f).symm⟩
  have hW (f : SΓ) : M (j f) = w f := rfl
  have hJ (f : SΓ) : N (w f) = j f :=
    (congrArg (fun g : S ↦ N g) (hW f).symm).trans (hNM (j f))
  with_reducible
    exact isotype_completion_of_projected_profiles (X := SΓ) (Y := S) Q hQQ i hi hd j w
      hwInj hfix hSurj M N hMcont hNcont hW hJ

omit hm hE hμ₁ hρ hi hd hcomm in
/-- Transport a structural pair and its presentation by a topological group
isomorphism, preserving the elementary Schwartz functions in the stage. -/
private theorem exists_schwartzBruhat_stage_pullback {A B : Type*} [CommGroup A] [CommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B]
    [T2Space A] [T2Space B] [LocallyCompactSpace A] [LocallyCompactSpace B] (e : A ≃ₜ* B)
    (a : BruhatStructuralPair B) (p : ElementaryLCAPresentation a.quotient) :
    ∃ (a' : BruhatStructuralPair A) (p' : ElementaryLCAPresentation a'.quotient)
      (j : SchwartzBruhatStage p →L[ℂ] SchwartzBruhatStage p'),
      ∀ f, schwartzBruhatStageRealization a p f ∘ e =
        schwartzBruhatStageRealization a' p' (j f) := by
  classical
  let dual : PontryaginDual B ≃ₜ* PontryaginDual A :=
    { toFun := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e)
      invFun := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
      left_inv := fun χ ↦ PontryaginDual.ext fun y ↦ congrArg χ (e.apply_symm_apply y)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (e.symm_apply_apply x)
      map_mul' := map_mul (PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e))
      continuous_toFun := (PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e)).continuous
      continuous_invFun := (PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)).continuous }
  let J := a.val.1
  let D := OrderDual.ofDual a.val.2
  let J' := J.comap e.toMulEquiv.toMonoidHom
  let D' := D.comap e.toMulEquiv.toMonoidHom
  let eJ : J' ≃ₜ* J := ContinuousMulEquiv.mk'
    (e.toHomeomorph.subtype fun _ ↦ Iff.rfl)
    (fun x y ↦ Subtype.ext (map_mul e (x : A) (y : A)))
  have hAnn (χ : PontryaginDual B) : χ ∈ lcaAnnihilator D ↔ dual χ ∈ lcaAnnihilator D' := by
    simp only [mem_lcaAnnihilator_iff]
    refine ⟨fun h x ↦ h ⟨e x, x.property⟩, fun h y ↦ ?_⟩
    have hy : e.symm y ∈ D' := by
      change e (e.symm y) ∈ D
      simpa only [e.apply_symm_apply] using y.property
    have heval : χ (e (e.symm y)) = 1 := h ⟨e.symm y, hy⟩
    simpa only [e.apply_symm_apply] using heval
  let eAnn : lcaAnnihilator D ≃ₜ* lcaAnnihilator D' := ContinuousMulEquiv.mk'
    (dual.toHomeomorph.subtype hAnn)
    (fun x y ↦ Subtype.ext (map_mul dual (x : PontryaginDual B) y))
  have hopen : IsOpen (lcaAnnihilator D' : Set (PontryaginDual A)) := by
    have heq : (lcaAnnihilator D' : Set (PontryaginDual A)) =
        dual.symm ⁻¹' (lcaAnnihilator D : Set (PontryaginDual B)) := by
      ext χ
      change χ ∈ lcaAnnihilator D' ↔ dual.symm χ ∈ lcaAnnihilator D
      rw [hAnn (dual.symm χ), dual.apply_symm_apply]
    rw [heq]
    exact a.property.2.2.1.2.1.preimage dual.symm.continuous
  let a' : BruhatStructuralPair A :=
    ⟨(J', OrderDual.toDual D'), a.property.1.preimage e.continuous,
      isCompactlyGeneratedGroup_of_continuousMulEquiv eJ.symm a.property.2.1,
      ⟨a.property.2.2.1.1.preimage e.continuous, hopen,
        isCompactlyGeneratedGroup_of_continuousMulEquiv eAnn a.property.2.2.1.2.2⟩,
      Subgroup.comap_mono a.property.2.2.2⟩
  let N := D.comap J.subtype
  let N' := D'.comap J'.subtype
  have hN : N'.map eJ.toMulEquiv.toMonoidHom = N := by
    change N'.map (eJ.toMulEquiv : J' →* J) = N
    rw [Subgroup.map_equiv_eq_comap_symm eJ.toMulEquiv]
    ext y
    change e (e.symm y) ∈ D ↔ (y : B) ∈ D
    rw [e.apply_symm_apply]
  let q := QuotientGroup.congr N' N eJ.toMulEquiv hN
  let eQ : a'.quotient ≃ₜ* a.quotient :=
    ⟨q, (QuotientGroup.isQuotientMap_mk N').continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp eJ.continuous),
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp eJ.symm.continuous)⟩
  let p' : ElementaryLCAPresentation a'.quotient := { p with equiv := eQ.trans p.equiv }
  refine ⟨a', p', ContinuousLinearMap.id ℂ _, fun f ↦ funext fun x ↦ ?_⟩
  change schwartzBruhatStageRealization a p f (e x) = schwartzBruhatStageRealization a' p' f x
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases hx : e x ∈ J
  · rw [dite_eq_left hx, dite_eq_left (show x ∈ a'.val.1 from hx)]
    rfl
  · rw [dite_eq_right hx, dite_eq_right (show x ∉ a'.val.1 from hx)]

omit hm hE hμ₁ hρ hi hd hcomm in
/-- Pullback by a topological group isomorphism is continuous on Schwartz–Bruhat
spaces. Each structural quotient uses the same elementary coordinates after pullback. -/
private theorem exists_schwartzBruhat_pullback {A B : Type*} [CommGroup A] [CommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B]
    [T2Space A] [T2Space B] [LocallyCompactSpace A] [LocallyCompactSpace B] (e : A ≃ₜ* B) :
    ∃ L : SchwartzBruhat B →L[ℂ] SchwartzBruhat A, ∀ f x, L f x = f (e x) := by
  classical
  let L : (B → ℂ) →ₗ[ℂ] (A → ℂ) := LinearMap.funLeft ℂ ℂ e
  have hle : schwartzBruhatSubmodule B ≤ (schwartzBruhatSubmodule A).comap L := by
    unfold schwartzBruhatSubmodule
    refine iSup_le fun a ↦ iSup_le fun p ↦ ?_
    rintro _ ⟨f, rfl⟩
    obtain ⟨a', p', j, hj⟩ := exists_schwartzBruhat_stage_pullback e a p
    change schwartzBruhatStageRealization a p f ∘ e ∈ schwartzBruhatSubmodule A
    rw [hj]
    exact (schwartzBruhatStageInclusion a' p' (j f)).property
  let M : SchwartzBruhat B →ₗ[ℂ] SchwartzBruhat A :=
    (L.comp (schwartzBruhatSubmodule B).subtype).codRestrict _ (fun f ↦ hle f.property)
  have hc : Continuous M := by
    refine (withGeneratingSeminorms_spec _ Subtype.val).continuous_of_continuous_comp M ?_
    rintro ⟨q, hq⟩
    let qM : Seminorm ℂ (schwartzBruhatSubmodule B) := q.comp M
    have hcomp (a : BruhatStructuralPair B) (p : ElementaryLCAPresentation a.quotient) :
        Continuous (qM ∘ schwartzBruhatStageInclusion a p) := by
      refine (exists_schwartzBruhat_stage_pullback e a p).elim fun a' hp ↦ ?_
      refine hp.elim fun p' hj' ↦ ?_
      refine hj'.elim fun j hj ↦ ?_
      have heq (f : SchwartzBruhatStage p) :
          schwartzBruhatStageInclusion a' p' (j f) = M (schwartzBruhatStageInclusion a p f) := by
        exact Subtype.ext (hj f).symm
      exact ((hq a' p').comp j.continuous).congr (fun f ↦ congrArg q (heq f))
    exact (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨qM, hcomp⟩
  exact ⟨⟨M, hc⟩, fun _ _ ↦ rfl⟩

omit hm hE hμ₁ hρ hi hd hcomm in
/-- On the Schwartz–Bruhat space, multiplication by a unitary character is
conjugate to translation on the dual via the Fourier transform. -/
private theorem exists_schwartzBruhat_characterEquiv (η : PontryaginDual G) :
    ∃ M : S ≃L[ℂ] S, ∀ (f : S) (x : G), M f x = (η x : ℂ) * f x := by
  let μ : Measure G := Measure.haar
  have : μ.IsHaarMeasure := inferInstanceAs ((Measure.haar (G := G)).IsHaarMeasure)
  have : μ.Regular := inferInstanceAs ((Measure.haar (G := G)).Regular)
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual G) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).secondCountableTopology
  have hFourier := schwartzBruhat_fourier_equiv μ
  let F := hFourier.choose
  have hF := hFourier.choose_spec
  let ρ := schwartzBruhatTranslationAction (G := PontryaginDual G)
  let T := ContinuousLinearEquiv.ofUnit (Units.map ρ (toUnits η))
  let M := (F.trans T).trans F.symm
  refine ⟨M, fun f x ↦ ?_⟩
  let g (y : G) : ℂ := (η y : ℂ) * f y
  have hη : Continuous (fun y : G ↦ (η y : ℂ)) := continuous_subtype_val.comp η.continuous
  have hg : Integrable g μ := by
    simpa only [g, mul_comm] using
      (hF f).1.mul_bdd (c := 1) hη.aestronglyMeasurable (.of_forall fun y ↦ by simp)
  have htransform (χ : PontryaginDual G) : lcaFourier μ (M f) χ = lcaFourier μ g χ := calc
    _ = F (M f) χ := ((hF (M f)).2 χ).symm
    _ = ρ η (F f) χ :=
      congrArg (fun v : SchwartzBruhat (PontryaginDual G) ↦ v χ)
        (F.apply_symm_apply (T (F f)))
    _ = F f (η⁻¹ * χ) := schwartzBruhatTranslationAction_apply η χ (F f)
    _ = lcaFourier μ f (η⁻¹ * χ) := (hF f).2 _
    _ = lcaFourier μ g χ := integral_congr_ae (ae_of_all _ fun y ↦ by
      change f y * star (((η y)⁻¹ * χ y : Circle) : ℂ) = g y * star (χ y : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul, star_star]
      dsimp only [g]
      ring)
  let u : G → ℂ := M f
  have hu : Integrable u μ := (hF (M f)).1
  have hz (χ : PontryaginDual G) : lcaFourier μ (u - g) χ = 0 := by
    change (∫ y, (u y - g y) * star (χ y : ℂ) ∂μ) = 0
    simp_rw [sub_mul]
    rw [integral_sub (integrable_fourierIntegrand μ hu χ) (integrable_fourierIntegrand μ hg χ)]
    exact sub_eq_zero.mpr (htransform χ)
  have hae : u =ᵐ[μ] g :=
    (ae_eq_zero_of_lcaFourier_eq_zero μ (hu.sub hg) hz).mono fun _ hy ↦ sub_eq_zero.mp hy
  exact congrFun (((continuous_schwartzBruhat (M f)).ae_eq_iff_eq μ
    (hη.mul (continuous_schwartzBruhat f))).mp hae) x

omit hE hρ hi hd hcomm in
/-- The normalized twisted coset integral is a quotient map onto the
Schwartz–Bruhat profiles, and evaluates the isotypic projector along the section. -/
private theorem exists_schwartzBruhat_isotype_profile (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ m) (ω : PontryaginDual K) :
    ∃ R : S →L[ℂ] SchwartzBruhat ℝ≥0ˣ, IsQuotientMap R ∧
      ∀ f t, R f t = schwartzBruhatIsotypicProjector m hm μ₁ ω f (τ t) := by
  let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
  let B := SchwartzBruhat ℝ≥0ˣ
  have hK : IsClosed (K : Set G) := hm.isCompact_ker.isClosed
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : LocallyCompactSpace K := inferInstance
  let : μ₁.Regular := inferInstance
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK
  let d : (G ⧸ K) ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse m.toMonoidHom τ hτ with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr m.continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp τ.continuous }
  let r : G →ₜ* K :=
    ⟨((MonoidHom.id G) / (τ.toMonoidHom.comp m.toMonoidHom)).codRestrict K (fun g ↦ by
        change m (g / τ (m g)) = 1
        rw [map_div, hτ (m g), div_self']),
      (continuous_id.div' (τ.continuous.comp m.continuous)).subtype_mk _⟩
  have hr (k : K) (t : ℝ≥0ˣ) : r ((k : G) * τ t) = k := by
    apply Subtype.ext
    change (k : G) * τ t / τ (m ((k : G) * τ t)) = k
    rw [map_mul, show m k = 1 from k.property, hτ t, one_mul, mul_div_cancel_right]
  let η := PontryaginDual.map r ω
  refine (exists_schwartzBruhat_characterEquiv η).elim fun M hM ↦ ?_
  refine (exists_schwartzBruhat_pullback d.symm).elim fun T hT ↦ ?_
  refine (exists_schwartzBruhat_pullback d).elim fun U hU ↦ ?_
  let D := ContinuousLinearEquiv.equivOfInverse T U
    (fun f ↦ Subtype.ext (funext fun q ↦ by rw [hU, hT, d.symm_apply_apply]))
    (fun f ↦ Subtype.ext (funext fun t ↦ by rw [hT, hU, d.apply_symm_apply]))
  refine (schwartzBruhatCosetIntegral_continuousLinear K μ₁ hK).elim fun A hA ↦ ?_
  have hAq : IsQuotientMap A := by
    let Q := SchwartzBruhat (G ⧸ K)
    have heq : (A : S → Q) = schwartzBruhatCosetIntegral K μ₁ hK :=
      funext hA
    exact Eq.mpr (congrArg (fun F : S → Q ↦ IsQuotientMap F) heq)
      (schwartzBruhatCosetIntegral_isQuotientMap K μ₁ hK)
  have hmass : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  let c : ℂˣ := Units.mk0 (((μ₁.real univ)⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero hmass))
  let N : B ≃L[ℂ] B := ContinuousLinearEquiv.smulLeft c
  let R : S →L[ℂ] B :=
    N.toContinuousLinearMap.comp (D.toContinuousLinearMap.comp (A.comp M.toContinuousLinearMap))
  have hRq : IsQuotientMap R :=
    N.toHomeomorph.isQuotientMap.comp
      (D.toHomeomorph.isQuotientMap.comp (hAq.comp M.toHomeomorph.isQuotientMap))
  refine ⟨R, hRq, fun f t ↦ ?_⟩
  let q : G ⧸ K := QuotientGroup.mk (τ t)
  let I (k : K) : ℂ := star (ω k : ℂ) * f ((k : G)⁻¹ * τ t)
  have hcoset : A (M f) q = ∫ k : K, M f (τ t * (k : G)) ∂μ₁ :=
    (congrArg (fun v : SchwartzBruhat (G ⧸ K) ↦ v q) (hA (M f))).trans
      (schwartzBruhatCosetIntegral_mk K μ₁ hK (M f) (τ t))
  have hpoint (k : K) : M f (τ t * (k : G)) = I k⁻¹ := calc
    _ = M f ((k : G) * τ t) := congrArg (fun x : G ↦ M f x) (mul_comm (τ t) (k : G))
    _ = (ω k : ℂ) * f ((k : G) * τ t) := by
      refine (hM f ((k : G) * τ t)).trans ?_
      change (ω (r ((k : G) * τ t)) : ℂ) * f ((k : G) * τ t) = _
      rw [hr k t]
    _ = I k⁻¹ := by
      dsimp only [I]
      rw [map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Subgroup.coe_inv, inv_inv]
  calc
    R f t = (↑c : ℂ) * T (A (M f)) t := rfl
    _ = (↑c : ℂ) * A (M f) q := congrArg ((↑c : ℂ) * ·) (hT (A (M f)) t)
    _ = (↑c : ℂ) * (∫ k : K, M f (τ t * (k : G)) ∂μ₁) := congrArg ((↑c : ℂ) * ·) hcoset
    _ = (↑c : ℂ) * (∫ k : K, I k⁻¹ ∂μ₁) :=
      congrArg ((↑c : ℂ) * ·) (integral_congr_ae (ae_of_all _ hpoint))
    _ = (↑c : ℂ) * (∫ k : K, I k ∂μ₁) := congrArg ((↑c : ℂ) * ·) (integral_inv_eq_self I μ₁)
    _ = (μ₁.real univ)⁻¹ • (∫ k : K, I k ∂μ₁) := Complex.real_smul.symm
    _ = P f (τ t) := (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω f (τ t)).2.symm

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
      ∀ f, e f = P.ker.mkQ (w f) := by
  let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
  let ρ := MonoidHom.comp (schwartzBruhatTranslationAction (G := G)) (Subgroup.subtype K)
  let k₀ (g : G) : K := ⟨g / τ (m g), by
    change m (g / τ (m g)) = 1
    rw [map_div, hτ (m g), div_self']⟩
  have hsplit (g : G) : (k₀ g : G) * τ (m g) = g := div_mul_cancel _ _
  refine (exists_schwartzBruhat_isotype_profile m hm μ₁ τ hτ ω).elim fun R h ↦ ?_
  have hRq := h.1
  have hR := h.2
  refine (schwartzBruhatIsotypicProjector_quotient_equiv m hm μ₁ ω).elim fun J hJ ↦ ?_
  have hmem (f : S) : P f ∈ actionIsotype ρ ω :=
    Eq.mp (congrArg (fun u : S ↦ u ∈ actionIsotype ρ ω) (hJ f)) (J (P.ker.mkQ f)).property
  have hhom (f : S) (k : K) (t : ℝ≥0ˣ) :
      P f ((k : G) * τ t) = star (ω k : ℂ) * R f t := by
    have hstar : (ω k⁻¹ : ℂ) = star (ω k : ℂ) := by
      rw [map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def]
    have hk : (((k⁻¹ : K) : G)⁻¹ * τ t) = (k : G) * τ t := by rw [Subgroup.coe_inv, inv_inv]
    calc
      _ = P f (((k⁻¹ : K) : G)⁻¹ * τ t) := congrArg (fun x : G ↦ P f x) hk.symm
      _ = ρ k⁻¹ (P f) (τ t) :=
        (schwartzBruhatTranslationAction_apply ((k⁻¹ : K) : G) (τ t) (P f)).symm
      _ = (ω k⁻¹ : ℂ) * P f (τ t) :=
        congrArg (fun u : S ↦ u (τ t)) ((mem_actionIsotype ρ ω (P f)).mp (hmem f) k⁻¹)
      _ = star (ω k : ℂ) * R f t := congrArg₂ (· * ·) hstar (hR f t).symm
  have hker : P.ker = R.ker := by
    ext f
    change P f = 0 ↔ R f = 0
    constructor
    · intro hf
      refine Subtype.ext (funext fun t ↦ ?_)
      exact (hR f t).trans (congrArg (fun u : S ↦ u (τ t)) hf)
    · intro hf
      refine Subtype.ext (funext fun g ↦ ?_)
      change P f g = 0
      calc
        _ = P f ((k₀ g : G) * τ (m g)) := congrArg (fun x : G ↦ P f x) (hsplit g).symm
        _ = star (ω (k₀ g) : ℂ) * R f (m g) := hhom f (k₀ g) (m g)
        _ = 0 := (congrArg (fun b : SchwartzBruhat ℝ≥0ˣ ↦ star (ω (k₀ g) : ℂ) * b (m g))
          hf).trans (mul_zero _)
  let L := P.ker.liftQL R hker.le
  have hLq : IsQuotientMap L :=
    P.ker.isQuotientMap_mkQL.of_comp_isQuotientMap hRq
  have hLi : Injective L := (LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' P.ker R.toLinearMap hker) : Injective L)
  let F := ContinuousLinearEquiv.ofIsHomeomorph
    (LinearEquiv.ofBijective L.toLinearMap ⟨hLi, hLq.surjective⟩)
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hLq, hLi⟩)
  let e := F.symm
  let w := (actionIsotype ρ ω).subtypeL.comp (J.toContinuousLinearMap.comp e.toContinuousLinearMap)
  have hwe (f : S) : w (R f) = P f :=
    (congrArg (fun q : S ⧸ P.ker ↦ (J q : S)) (F.symm_apply_apply (P.ker.mkQ f))).trans (hJ f)
  refine ⟨w, e, ?_, ?_⟩
  · refine hRq.surjective.forall.mpr fun g k t ↦ ?_
    exact (congrArg (fun u : S ↦ u ((k : G) * τ t)) (hwe g)).trans (hhom g k t)
  · intro f
    apply J.injective
    apply Subtype.ext
    change w f = (J (P.ker.mkQ (w f)) : S)
    exact ((hJ (w f)).trans
      (schwartzBruhatIsotypicProjector_apply_isotype m hm μ₁ ω (w f) (J (e f)).property)).symm

-- TODO(paper-gap): Corollary D.2.2.3(2) drops the density hypothesis.
-- For the trivial character, the injection into S(G) × ℂ with zero
-- second coordinate leaves the added trivial summand outside the closure.

end SplitModule

end RiemannMasullo
