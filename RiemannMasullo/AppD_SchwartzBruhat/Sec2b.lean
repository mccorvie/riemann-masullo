module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1d
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
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

include hE hρ heq hi hcomm hQ

/-- Paper: Lemma D.2.2.1(1), p. 795. The kernel of averaging on the target
pulls back to the kernel of averaging on the source. -/
theorem schwartzBruhatIsotype_comap_ker : Q.ker.comap i.toLinearMap = (P).ker := by sorry

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
  exact denseRange_isotype_of_pettisAverage (H := K) (X := S) (Y := E) μ₁ ω ρS ρE hρK
    (μ₁.real univ • Q) hQ hcompact havg i hi hintertwines hd j hj

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
  let P' := schwartzBruhatIsotypicProjector m hm μ₁ χ
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  have hmass : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  have hi_average (ξ : PontryaginDual K) (B : E →L[ℂ] E)
      (hB : IsPettisIsotypicAverageOn μ₁ univ ρE ξ (μ₁.real univ • B)) (f : S) :
      i (schwartzBruhatIsotypicProjector m hm μ₁ ξ f) = B (i f) := by
    refine (exists_schwartzBruhatIsotypicProjector_average m hm μ₁ (hμ₁ := hμ₁) ξ).elim ?_
    intro A hA
    have hUnique := existsUnique_schwartzBruhatIsotypicProjector m hm μ₁ (hμ₁ := hμ₁) ξ
    have hproj : A = schwartzBruhatIsotypicProjector m hm μ₁ ξ :=
      hUnique.unique hA.1 (Classical.choose_spec hUnique.exists)
    have havg : i ((μ₁.real univ • A) f) = (μ₁.real univ • B) (i f) := by
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
      intro φ
      let F (k : K) : ℂ := φ (star (ξ k : ℂ) • ρE k (i f))
      calc
        φ (i ((μ₁.real univ • A) f)) =
            ∫ k, φ (i (star (ξ k : ℂ) • ρS k f)) ∂μ₁ :=
          pettisIntegral_univ_eval (hA.2 f) (φ.comp i)
        _ = ∫ k, F k ∂μ₁ := integral_congr_ae (ae_of_all _ fun k ↦ by
          refine congrArg φ ((i.map_smul (star (ξ k : ℂ)) (ρS k f)).trans ?_)
          exact congrArg (fun v : E ↦ star (ξ k : ℂ) • v) (hcomm (k : G) f))
        _ = φ ((μ₁.real univ • B) (i f)) := (pettisIntegral_univ_eval (hB (i f)) φ).symm
    refine (congrArg (fun L : S →L[ℂ] S ↦ i (L f)) hproj.symm).trans ?_
    exact smul_right_injective E hmass
      ((i.map_smul_of_tower (μ₁.real univ) (A f)).symm.trans havg)
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
  exact existsUnique_isotype_quotient_maps P P' T Q Q' U i hTP hUQ hU

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
