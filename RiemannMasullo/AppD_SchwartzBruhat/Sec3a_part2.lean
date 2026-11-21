module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
import all RiemannMasullo.AppC_LCTVS.Sec1
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b

/-!
# Structure and Fourier–Mellin transform of Schwartz–Bruhat decay spaces

Masullo, Appendix D, §D.3.3, from the end of Example D.3.3.5.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Function MeasureTheory Set Topology TopologicalSpace UniformSpace
open scoped Manifold NNReal TensorProduct

-- TODO(later): needs §B.2
-- Lemma D.3.2.3(4)–(6) uses the three decay spaces in Definition B.2.1.1, p. 593.

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local instance {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}
    (p : SeminormFamily ℂ X ι) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

/-- Paper: Example D.3.3.5, p. 805. Pullback along the quotient map for nested
compact subgroups with compactly generated annihilators is a topological embedding
on the ordinary Schwartz–Bruhat spaces. -/
theorem schwartzBruhat_compactQuotient_pullback [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (k k' : GoodCompact) (h : k'.val ≤ k.val) :
    ∃ j : SchwartzBruhat (G ⧸ k.val) →L[ℂ] SchwartzBruhat (G ⧸ k'.val),
      IsEmbedding j ∧ ∀ f (g : G), j f (g : G ⧸ k'.val) = f (g : G ⧸ k.val) := by
  sorry

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ)

local notation "K" => m.toMonoidHom.ker
local notation "E" => ModulatedExponentialDecay m I
local notation "P" => PositiveRealExponentialDecay I

section Stages

/-- Paper: (D.3.3.2), p. 805. The topology of a decay stage is induced by the
joint map to the product of its Schwartz–Bruhat twists. -/
private theorem modulatedExponentialDecayStage_twists_isInducing (k : GoodCompact) :
    IsInducing (fun (f : ModulatedExponentialDecayStage m I k) (a : I) ↦
      modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I a f) := by
  let T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (I → SchwartzBruhat (G ⧸ k.val)) :=
    LinearMap.pi (modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I)
  change IsInducing T
  have hPi := withSeminorms_pi
    (fun _ : I ↦ PolynormableSpace.withSeminorms ℂ (SchwartzBruhat (G ⧸ k.val)))
  have hInduced := WithSeminorms.topologicalSpace_eq_iInf (t := induced T inferInstance)
    (T.withSeminorms_induced hPi)
  refine ⟨(withGeneratingSeminorms_spec _ _).topologicalSpace_eq_iInf.trans
    (Eq.trans ?_ hInduced.symm)⟩
  exact (Equiv.sigmaEquivProd I _).symm.iInf_congr (fun _ ↦ rfl)

variable (hm : IsModulation m) (hms : Surjective m) (hInt : OrdConnected I) (hne : I.Nonempty)

set_option linter.unusedSectionVars false in
include hm hms hInt hne in
/-- Paper: Example D.3.3.5, p. 805. When k' is contained in k, pullback
from G/k to G/k' embeds the decay stage topologically in the larger stage. -/
theorem modulatedExponentialDecayStage_transition (k k' : GoodCompact) (h : k'.val ≤ k.val) :
    ∃ j : ModulatedExponentialDecayStage m I k →L[ℂ] ModulatedExponentialDecayStage m I k',
      IsEmbedding j ∧ ∀ f (g : G), (j f).val (g : G ⧸ k'.val) = f.val (g : G ⧸ k.val) := by
  have hSchwartz := schwartzBruhat_compactQuotient_pullback (G := G) k k' h
  let L := hSchwartz.choose
  have hL : IsEmbedding L := hSchwartz.choose_spec.1
  have hL_apply := hSchwartz.choose_spec.2
  let n := quotientModulation m k.val k.property.1
  let n' := quotientModulation m k'.val k'.property.1
  let q : (G ⧸ k'.val) →* (G ⧸ k.val) :=
    QuotientGroup.map k'.val k.val (MonoidHom.id G) (by simpa only [Subgroup.comap_id] using h)
  let pullback : ModulatedExponentialDecayStage m I k →ₗ[ℂ] ((G ⧸ k'.val) → ℂ) :=
    (LinearMap.pi fun x ↦ LinearMap.proj (q x)).comp
      (modulatedExponentialDecaySubmodule n I).subtype
  have hweight (f : ModulatedExponentialDecayStage m I k) (a : I) :
      modulationWeight n' a (pullback f) =
        (L (modulatedExponentialDecayTwist n I a f) : (G ⧸ k'.val) → ℂ) := by
    funext x
    exact QuotientGroup.induction_on x fun g ↦
      (hL_apply (modulatedExponentialDecayTwist n I a f) g).symm
  let j : ModulatedExponentialDecayStage m I k →ₗ[ℂ] ModulatedExponentialDecayStage m I k' :=
    pullback.codRestrict (modulatedExponentialDecaySubmodule n' I) (by
      intro f
      refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr ?_
      rw [hweight]
      exact (L (modulatedExponentialDecayTwist n I a f)).property)
  let twists (f : ModulatedExponentialDecayStage m I k) (a : I) :=
    modulatedExponentialDecayTwist n I a f
  let twists' (f : ModulatedExponentialDecayStage m I k') (a : I) :=
    modulatedExponentialDecayTwist n' I a f
  let mapTwists := Pi.map fun _ : I ↦
    (L : SchwartzBruhat (G ⧸ k.val) → SchwartzBruhat (G ⧸ k'.val))
  have hcomm : twists' ∘ j = mapTwists ∘ twists :=
    funext fun f ↦ funext fun a ↦ Subtype.ext (hweight f a)
  have hmapTwists : IsInducing mapTwists := IsInducing.piMap fun _ ↦ hL.isInducing
  have hcomposite : IsInducing (twists' ∘ j) :=
    Eq.mpr (congrArg (fun φ : ModulatedExponentialDecayStage m I k →
      I → SchwartzBruhat (G ⧸ k'.val) ↦ IsInducing φ) hcomm)
      (hmapTwists.comp (modulatedExponentialDecayStage_twists_isInducing m I k))
  have htwists' : IsInducing twists' := modulatedExponentialDecayStage_twists_isInducing m I k'
  have hj : IsInducing j := htwists'.of_comp_iff.mp hcomposite
  refine ⟨⟨j, hj.continuous⟩, ⟨hj, ?_⟩, fun _ _ ↦ rfl⟩
  intro f g hfg
  apply Subtype.ext
  funext x
  exact QuotientGroup.induction_on x fun y ↦
    congrArg (fun z : ModulatedExponentialDecayStage m I k' ↦ z.val (y : G ⧸ k'.val)) hfg

variable [hSC : SecondCountableTopology G]

/-- Paper: Example D.3.3.5, p. 805. The compact components of a cofinal sequence of
Bruhat structural pairs are cofinal among compact subgroups with compactly generated annihilator. -/
private theorem exists_antitone_goodCompact :
    ∃ k : ℕ → GoodCompact, Antitone (fun n ↦ (k n).val) ∧
      ∀ k' : GoodCompact, ∃ n, (k n).val ≤ k'.val := by
  obtain ⟨a, _, _, ha, hcof, _⟩ := schwartzBruhat_exists_topologicallyExact (G := G)
  let subgroup (n : ℕ) := OrderDual.ofDual (a n).val.2
  have hgood (n : ℕ) : IsBruhatGoodSubgroup (subgroup n) := (a n).property.2.2.1
  have hcomp (n : ℕ) : IsCompact (subgroup n : Set G) := by
    obtain ⟨_, _, _, hker, hc⟩ := lca_dualSubgroup_quotient
      (⟨lcaAnnihilator (subgroup n), (hgood n).2⟩ : OpenCompactlyGeneratedSubgroups (PontryaginDual G))
    rwa [hker, lcaDualAnnihilator_annihilator (subgroup n) (hgood n).1] at hc
  refine ⟨fun n ↦ ⟨subgroup n, hcomp n, (hgood n).2.2⟩, fun _ _ h ↦ (ha h).2, ?_⟩
  intro k'
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains k'.property.1
  let b : BruhatStructuralPair G := ⟨(H.val, OrderDual.toDual k'.val), H.property.1,
    H.property.2, ⟨k'.property.1.isClosed, isOpen_lcaAnnihilator _ k'.property.1,
      k'.property.2⟩, hH⟩
  obtain ⟨n, hn⟩ := hcof b
  exact ⟨n, hn.2⟩

/-- A decreasing cofinal sequence of indices for a family of embedded stages has the
same union and final locally convex topology, and its maps into the union are embeddings. -/
private theorem stageLimit_of_cofinal {ι : Type*} [Preorder ι]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [t : TopologicalSpace F] [IsTopologicalAddGroup F]
    {X : ι → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, PolynormableSpace ℂ (X a)]
    (i : ∀ a, X a →ₗ[ℂ] F) (hinj : ∀ a, Injective (i a))
    (hex : ∀ x : F, ∃ a, x ∈ (i a).range) (ht : t = locallyConvexFinalTopology i)
    (htrans : ∀ a b, b ≤ a → ∃ j : X a →L[ℂ] X b,
      IsEmbedding j ∧ ∀ x, i b (j x) = i a x)
    (k : ℕ → ι) (hk : Antitone k) (hcof : ∀ a, ∃ n, k n ≤ a) :
    (∀ n, IsEmbedding (i (k n))) ∧ (∀ x : F, ∃ n, x ∈ (i (k n)).range) ∧
      t = locallyConvexFinalTopology (fun n ↦ i (k n)) := by
  have hfactor (a : ι) : ∃ n, ∃ j : X a →L[ℂ] X (k n), ∀ x, i (k n) (j x) = i a x := by
    obtain ⟨n, hn⟩ := hcof a
    obtain ⟨j, _, hj⟩ := htrans a (k n) hn
    exact ⟨n, j, hj⟩
  have hcover (x : F) : ∃ n, x ∈ (i (k n)).range := by
    obtain ⟨a, y, rfl⟩ := hex x
    obtain ⟨n, j, hj⟩ := hfactor a
    exact ⟨n, j y, hj y⟩
  have htests : (fun p : Seminorm ℂ F ↦ ∀ a, Continuous (p ∘ i a)) =
      (fun p : Seminorm ℂ F ↦ ∀ n, Continuous (p ∘ i (k n))) := by
    funext p
    apply propext
    refine ⟨fun h n ↦ h (k n), fun h a ↦ ?_⟩
    obtain ⟨n, j, hj⟩ := hfactor a
    exact ((h n).comp j.continuous).congr fun x ↦ congrArg p (hj x)
  have ht' : t = locallyConvexFinalTopology (fun n ↦ i (k n)) :=
    ht.trans (congrArg (fun pred : Seminorm ℂ F → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype pred → Seminorm ℂ F)).topology) htests)
  have hseminorms : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ F // ∀ a, Continuous (p ∘ i a)} → Seminorm ℂ F) := ⟨ht⟩
  let incl (n : ℕ) : X (k n) →L[ℂ] F :=
    ⟨i (k n), hseminorms.continuous_of_continuous_comp _ fun p ↦ p.property (k n)⟩
  choose j hj hcomm using fun n ↦ htrans (k n) (k (n + 1)) (hk (Nat.le_succ n))
  have hlim : IsInjectiveLCLimit (X := fun n ↦ X (k n)) j incl :=
    ⟨fun n ↦ hinj (k n), fun n ↦ ContinuousLinearMap.ext (hcomm n), hcover, ht'⟩
  exact ⟨hlim.isEmbedding_stage hj, hcover, ht'⟩

-- Checking unused section variables traverses the expanded seminorm families.
set_option linter.unusedSectionVars false in
include hSC hm hms hInt hne in
/-- Paper: Example D.3.3.5, p. 805. A decreasing cofinal sequence of stages
presents the decay space as a strict locally convex inductive limit. -/
theorem modulatedExponentialDecay_stageLimit :
    ∃ k : ℕ → GoodCompact,
      let i (n : ℕ) : ModulatedExponentialDecayStage m I (k n) →ₗ[ℂ] E :=
        modulatedExponentialDecayStageInclusion m I (k n)
      Antitone (fun n ↦ (k n).val) ∧ (∀ k' : GoodCompact, ∃ n, (k n).val ≤ k'.val) ∧
      (∀ n, IsEmbedding (i n)) ∧ (∀ f : E, ∃ n, f ∈ (i n).range) ∧
      (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology i := by
  have hc := exists_antitone_goodCompact (G := G)
  let k := hc.choose
  exact ⟨k, hc.choose_spec.1, hc.choose_spec.2,
    stageLimit_of_cofinal (F := E) (X := ModulatedExponentialDecayStage m I)
      (fun a ↦ modulatedExponentialDecayStageInclusion m I a)
      (fun a ↦ (modulatedExponentialDecayStageInclusion_range m I a).1)
      (modulatedExponentialDecay_exists_stage m I hm hms hInt hne) rfl
      (fun a b h ↦ (modulatedExponentialDecayStage_transition m I hm hms hInt hne a b h).imp
        fun _ hj ↦ ⟨hj.1, fun f ↦ Subtype.ext (funext (hj.2 f))⟩)
      k hc.choose_spec.1 hc.choose_spec.2⟩

/-- Point evaluation on the Schwartz–Bruhat space is continuous since on each
structural stage it is bounded by the zeroth Schwartz seminorm. -/
private theorem continuous_schwartzBruhat_eval {A : Type*} [CommGroup A] [TopologicalSpace A]
    (x : A) : Continuous (fun f : SchwartzBruhat A ↦ f x) := by
  let ev : SchwartzBruhat A →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule A).subtype
  let p : Seminorm ℂ (SchwartzBruhat A) := (normSeminorm ℂ ℂ).comp ev
  have hp : Continuous p := by
    apply (withGeneratingSeminorms_spec _ _).continuous_seminorm
      (⟨p, ?_⟩ : {p : Seminorm ℂ (schwartzBruhatSubmodule A) //
        ∀ (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient),
          Continuous (p ∘ schwartzBruhatStageInclusion a e)})
    intro a e
    let _ := e.finiteGroup
    let i : ElementarySchwartzIndex e.realDim e.torusDim e.latticeRank := (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e) :
      Seminorm ℂ (SchwartzBruhatStage e))
    refine Seminorm.continuous_of_le («E» := SchwartzBruhatStage e)
      (q := elementarySchwartzSeminorm i) (elementarySchwartz_withSeminorms.continuous_seminorm i) ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ elementarySchwartzSeminorm i f
    classical
    erw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f.val y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
      apply ENNReal.toReal_mono (f.property.2 i).ne
      rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f.val z‖₊ : ENNReal)) y
    · exact (norm_zero («E» := ℂ)).le.trans (apply_nonneg (elementarySchwartzSeminorm i) f)
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp («E» := SchwartzBruhat A) ev
    (fun _ ↦ hp)

/-- The joint twist map has closed range because its coordinates obey pointwise
compatibility equations with any one fixed twist. -/
private theorem modulatedExponentialDecayTwists_closedRange {A : Type*} [CommGroup A]
    [TopologicalSpace A] (n : A →ₜ* ℝ≥0ˣ) (J : Set ℝ) (hJ : J.Nonempty) :
    IsClosed (range (fun (f : modulatedExponentialDecaySubmodule n J) (b : J) ↦
      modulatedExponentialDecayTwist n J b f)) := by
  let twists (f : modulatedExponentialDecaySubmodule n J) (b : J) :=
    modulatedExponentialDecayTwist n J b f
  change IsClosed (range twists)
  obtain ⟨a, ha⟩ := hJ
  let a₀ : J := ⟨a, ha⟩
  let w (b : J) (x : A) : ℂ := ((((n x).val : ℝ) ^ (b : ℝ) : ℝ) : ℂ)
  have hw (b : J) (x : A) : w b x ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n x))) _).ne'
  have heval (b : J) (x : A) :
      Continuous (fun g : J → SchwartzBruhat A ↦ g b x) := by
    have hb : Continuous (fun g : J → SchwartzBruhat A ↦ g b) := continuous_apply b
    exact (continuous_schwartzBruhat_eval (A := A) x).comp hb
  let compatible (b : J) (x : A) : Set (J → SchwartzBruhat A) :=
    {g | w a₀ x * g b x = w b x * g a₀ x}
  have hrange : range twists = ⋂ (b : J) (x : A), compatible b x := by
    refine Set.ext fun g ↦ ?_
    simp only [mem_range, mem_iInter, compatible, mem_ofPred_eq]
    constructor
    · rintro ⟨f, rfl⟩ b x
      change w a₀ x * (w b x * f.val x) = w b x * (w a₀ x * f.val x)
      exact mul_left_comm _ _ _
    · intro hg
      let f (x : A) := g a₀ x / w a₀ x
      have hmatch (b : J) (x : A) : w b x * f x = g b x := by
        change w b x * (g a₀ x / w a₀ x) = g b x
        rw [← mul_div_assoc]
        exact (div_eq_iff (hw a₀ x)).mpr ((hg b x).symm.trans (mul_comm _ _))
      have hf : f ∈ modulatedExponentialDecaySubmodule n J := by
        refine (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr ?_
        let gb : schwartzBruhatSubmodule A := g b
        have hb : modulationWeight n b f = gb.val := funext (hmatch b)
        exact hb ▸ gb.property
      refine ⟨⟨f, hf⟩, ?_⟩
      funext b
      exact Subtype.ext (funext (hmatch b))
  have hCompatible (b : J) (x : A) : IsClosed (compatible b x) :=
    isClosed_eq (continuous_const.mul (heval b x)) (continuous_const.mul (heval a₀ x))
  have hIntersection : IsClosed (⋂ (b : J) (x : A), compatible b x) :=
    isClosed_iInter fun b ↦ isClosed_iInter (hCompatible b)
  exact (congrArg (fun s : Set (J → SchwartzBruhat A) ↦ IsClosed s) hrange).mpr hIntersection

set_option linter.unusedSectionVars false in
include hSC hm hms hInt hne in
/-- Paper: Example D.3.3.5, p. 806. Each compact-subgroup decay stage is complete. -/
theorem modulatedExponentialDecayStage_complete (k : GoodCompact) :
    CompleteSpace (ModulatedExponentialDecayStage m I k) := by
  let n := quotientModulation m k.val k.property.1
  let T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (I → SchwartzBruhat (G ⧸ k.val)) :=
    LinearMap.pi (modulatedExponentialDecayTwist n I)
  have hInd : IsInducing T := modulatedExponentialDecayStage_twists_isInducing m I k
  have hT : IsUniformInducing T := AddMonoidHom.isUniformInducing_of_isInducing
    (f := T) hInd
  have hClosed : IsClosed (range T) :=
    modulatedExponentialDecayTwists_closedRange n I hne
  let _ : IsClosed (k.val : Set G) := k.property.1.isClosed
  let _ := schwartzBruhat_complete (G := G ⧸ k.val)
  exact hT.completeSpace hClosed.isComplete

set_option linter.unusedSectionVars false in
include hm hms hInt hne in
/-- Paper: Remark D.3.3.6, p. 806. Multiplying by the module to the power a
moves the decay interval to its translate by -a and gives a topological isomorphism. -/
theorem modulatedExponentialDecay_shift_equiv (a : ℝ) :
    ∃ e : E ≃L[ℂ] ModulatedExponentialDecay m ((fun b : ℝ ↦ b - a) '' I),
      ∀ f, (e f).val = modulationWeight m a f.val := by
  have weight_add {A : Type _} [CommGroup A] [TopologicalSpace A]
      (n : A →ₜ* ℝ≥0ˣ) (b c : ℝ) (f : A → ℂ) :
      modulationWeight n b (modulationWeight n c f) = modulationWeight n (b + c) f := by
    funext x
    have hx : 0 < ((n x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (n x))
    simp only [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply,
      Real.rpow_add hx, Complex.ofReal_mul, mul_assoc]
  let shift {A : Type _} [CommGroup A] [TopologicalSpace A]
      (n : A →ₜ* ℝ≥0ˣ) (S T : Set ℝ) (c : ℝ) (h : ∀ b ∈ T, b + c ∈ S) :
      modulatedExponentialDecaySubmodule n S →ₗ[ℂ] modulatedExponentialDecaySubmodule n T :=
    ((modulationWeight n c).comp (modulatedExponentialDecaySubmodule n S).subtype).codRestrict
      (modulatedExponentialDecaySubmodule n T) (by
        intro f
        refine (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr ?_
        change modulationWeight n b (modulationWeight n c f.val) ∈ schwartzBruhatSubmodule A
        rw [weight_add]
        exact modulationWeight_mem_schwartzBruhat n S ⟨b + c, h b b.property⟩ f)
  let continuousShift (S T : Set ℝ) (c : ℝ) (h : ∀ b ∈ T, b + c ∈ S) :
      ModulatedExponentialDecay m S →L[ℂ] ModulatedExponentialDecay m T := by
    let F : ModulatedExponentialDecay m S →ₗ[ℂ] ModulatedExponentialDecay m T := shift m S T c h
    refine ⟨F, ?_⟩
    change Continuous F
    let FinalSeminorms (U : Set ℝ) := {q : Seminorm ℂ (modulatedExponentialDecaySubmodule m U) //
      ∀ k : GoodCompact, Continuous (q ∘ modulatedExponentialDecayStageInclusion m U k)}
    have generating (U : Set ℝ) :=
      withGeneratingSeminorms_spec _ (Subtype.val : FinalSeminorms U → _)
    refine (generating T).continuous_of_continuous_comp F fun p ↦ ?_
    let q : Seminorm ℂ (ModulatedExponentialDecay m S) := p.val.comp F
    change Continuous q
    have hq (k : GoodCompact) : Continuous (q ∘ modulatedExponentialDecayStageInclusion m S k) := by
      let n := quotientModulation m k.val k.property.1
      let stageShift : ModulatedExponentialDecayStage m S k →ₗ[ℂ]
          ModulatedExponentialDecayStage m T k := shift n S T c h
      have hstage : Continuous stageShift := by
        apply (modulatedExponentialDecayStage_twists_isInducing m T k).continuous_iff.mpr
        apply continuous_pi
        intro b
        let d : S := ⟨b + c, h b b.property⟩
        have htwist : Continuous (fun f : ModulatedExponentialDecayStage m S k ↦
            modulatedExponentialDecayTwist n S d f) :=
          (continuous_apply d).comp (modulatedExponentialDecayStage_twists_isInducing m S k).continuous
        exact htwist.congr fun f ↦ Subtype.ext (weight_add n b c f.val).symm
      exact ((p.property k).comp hstage).congr fun f ↦ congrArg p.val (Subtype.ext rfl)
    exact (generating S).continuous_seminorm (⟨q, hq⟩ : FinalSeminorms S)
  let J := (fun b : ℝ ↦ b - a) '' I
  have hforward : ∀ b ∈ J, b + a ∈ I := by
    rintro b ⟨d, hd, rfl⟩
    simpa only [sub_add_cancel] using hd
  have hbackward : ∀ b ∈ I, b + -a ∈ J := by
    intro b hb
    exact ⟨b, hb, sub_eq_add_neg b a⟩
  let forward : E →L[ℂ] ModulatedExponentialDecay m J := continuousShift I J a hforward
  let backward : ModulatedExponentialDecay m J →L[ℂ] E := continuousShift J I (-a) hbackward
  have hleft : LeftInverse backward forward := by
    intro f
    apply Subtype.ext
    change modulationWeight m (-a) (modulationWeight m a f.val) = f.val
    rw [weight_add, neg_add_cancel, modulationWeight_zero]
  have hright : RightInverse backward forward := by
    intro f
    apply Subtype.ext
    change modulationWeight m a (modulationWeight m (-a) f.val) = f.val
    rw [weight_add, add_neg_cancel, modulationWeight_zero]
  exact ⟨ContinuousLinearEquiv.equivOfInverse forward backward hleft hright, fun _ ↦ rfl⟩

include hm hms in
/-- Paper: Remark D.3.3.6, p. 806. Multiplication by a continuous quasi-character
is a topological automorphism of the space with two-sided exponential decay. -/
theorem modulatedExponentialDecay_mul_quasiCharacter (c : QuasiCharacter G) :
    ∃ e : ModulatedExponentialDecay m univ ≃L[ℂ] ModulatedExponentialDecay m univ,
      ∀ f g, (e f).val g = c g * f.val g := by sorry

end Stages

section Structure

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

include hτ in
/-- Paper: §D.3.3.1, p. 806. A splitting gives each quasi-character in the
relative strip a unique pair of coordinates, a kernel character and an exponent in the strip. -/
theorem modulatedExponentialDecay_strip_coordinates
    (c : relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I) :
    ∃! p : PontryaginDual K × ℂ, p.2.re ∈ I ∧
      ∀ (u : K) (t : ℝ≥0ˣ),
        (c : QuasiCharacter G) ((u : G) * τ t) = (p.1 u : ℂ) * ((t.val : ℝ) : ℂ) ^ p.2 :=
  by sorry

local notation "T" => InductiveTensor (SchwartzBruhat K) P

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The splitting of the modulation induces
the completed inductive tensor isomorphism, given by multiplication in split coordinates. -/
theorem modulatedExponentialDecay_tensor_equiv :
    ∃ e : Completion T ≃L[ℂ] E,
      ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
        (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
          h u * f.val (Real.log (t.val : ℝ)) := by sorry

include hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The tensor isomorphism intertwines
translation in each factor with translation on G. -/
theorem modulatedExponentialDecay_tensor_equivariant
    (e : Completion T ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
        h u * f.val (Real.log (t.val : ℝ))) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    letI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
    ∀ (u : K) (t : ℝ≥0ˣ), ∃ L : P →L[ℂ] P,
      (∀ f x, (L f).val x = f.val (x - Real.log (t.val : ℝ))) ∧
      ∀ z : Completion T, ∀ g : G,
        (e (Completion.map (inductiveTensorMap
          ((schwartzBruhatTranslationAction (G := K)) u).toLinearMap L.toLinearMap : T → T) z)
          ).val g = (e z).val (((u : G) * τ t)⁻¹ * g) := by sorry

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The tensor isomorphism on a quotient
stage commutes with the two inclusions into the full spaces.
Deviation: The subgroup on the norm-one factor is the restriction of k to that factor. -/
theorem modulatedExponentialDecay_tensor_stage
    (e : Completion T ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
        h u * f.val (Real.log (t.val : ℝ)))
    (k : GoodCompact) :
    let k₁ := k.val.comap (Subgroup.subtype K)
    let Tₖ := InductiveTensor (SchwartzBruhat (K ⧸ k₁)) P
    ∃ (eₖ : Completion Tₖ ≃L[ℂ] ModulatedExponentialDecayStage m I k)
      (j : SchwartzBruhat (K ⧸ k₁) →L[ℂ] SchwartzBruhat K),
      (∀ h u, j h u = h (u : K ⧸ k₁)) ∧
      (∀ (h : SchwartzBruhat (K ⧸ k₁)) (f : P) (u : K) (t : ℝ≥0ˣ),
        (eₖ (Completion.coe' (α := Tₖ) (h ⊗ₜ[ℂ] f))).val
          (((u : G) * τ t : G) : G ⧸ k.val) = h (u : K ⧸ k₁) * f.val (Real.log (t.val : ℝ))) ∧
      Continuous (modulatedExponentialDecayStageInclusion m I k :
        ModulatedExponentialDecayStage m I k → E) ∧
      ∀ z : Completion Tₖ,
        modulatedExponentialDecayStageInclusion m I k (eₖ z) =
          e (Completion.map (inductiveTensorMap j.toLinearMap
            (LinearMap.id : P →ₗ[ℂ] P) : Tₖ → T) z) := by sorry

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The comparison from the completed
inductive tensor product at a compact-subgroup stage to the completed
projective tensor product is a topological isomorphism. -/
theorem modulatedExponentialDecay_stage_tensor_comparison (k : GoodCompact) :
    let Q := SchwartzBruhat (K ⧸ k.val.comap (Subgroup.subtype K))
    IsHomeomorph (@Completion.map (InductiveTensor Q P) _ (ProjectiveTensor Q P) _ id) :=
  by sorry

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. A bounded family in the full decay
space is the image of a bounded family in one compact-subgroup stage. -/
theorem modulatedExponentialDecay_bounded_image_stage {B : Set E} (hB : IsVonNBounded ℂ B) :
    ∃ (k : GoodCompact) (C : Set (ModulatedExponentialDecayStage m I k)),
      IsVonNBounded ℂ C ∧ modulatedExponentialDecayStageInclusion m I k '' C = B := by sorry

include hSC hm hInt hne hτ

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is a strict LF-space. -/
theorem modulatedExponentialDecay_strictLF : IsStrictLFSpace E := by sorry

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is complete. -/
theorem modulatedExponentialDecay_complete : CompleteSpace E := by sorry

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is nuclear. -/
theorem modulatedExponentialDecay_nuclear : IsNuclearTVS E := by sorry

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is Montel and barrelled. -/
theorem modulatedExponentialDecay_montel : BarrelledSpace ℂ E ∧ MontelSpace ℂ E := by sorry

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is bornological,
expressed by continuity of seminorms bounded on every bounded set. -/
theorem modulatedExponentialDecay_bornological :
    ∀ p : Seminorm ℂ E,
      (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p := by sorry

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is Fréchet when
the norm-one subgroup has compactly generated dual. -/
theorem modulatedExponentialDecay_frechet
    (hK : IsCompactlyGeneratedGroup (PontryaginDual K)) : IsFrechetTVS E := by sorry

/-- Paper: Theorem D.3.3.7(3), p. 807. The Hausdorff strong dual of the decay
space is complete. -/
theorem modulatedExponentialDecay_strongDual_complete :
    CompleteSpace (StrongDual ℂ E) := by sorry

/-- Paper: Theorem D.3.3.7(3), p. 807. The strong dual is nuclear. -/
theorem modulatedExponentialDecay_strongDual_nuclear :
    IsNuclearTVS (StrongDual ℂ E) := by sorry

/-- Paper: Theorem D.3.3.7(3), p. 807. The strong dual is Montel and barrelled. -/
theorem modulatedExponentialDecay_strongDual_montel :
    BarrelledSpace ℂ (StrongDual ℂ E) ∧ MontelSpace ℂ (StrongDual ℂ E) := by sorry

/-- Paper: Theorem D.3.3.7(4), p. 807. If zero belongs to the interval,
the decay space includes continuously into the ordinary Schwartz–Bruhat space. -/
theorem modulatedExponentialDecay_continuous_inclusion (h0 : 0 ∈ I) :
    ∃ j : E →L[ℂ] SchwartzBruhat G, Injective j ∧ ∀ f g, j f g = f.val g := by sorry

/-- Paper: Theorem D.3.3.7(4), p. 807. For a compact interval,
the topology is induced by the family of weighted Schwartz–Bruhat profiles. -/
theorem modulatedExponentialDecay_compact_projective_topology (hI : IsCompact I) :
    IsEmbedding (fun (f : E) (a : I) ↦ modulatedExponentialDecayTwist m I a f) := by sorry

end Structure

section BoundedSets

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

-- Remark D.3.3.8 is the cofinality assertion in modulatedExponentialDecay_stageLimit.
-- Remark D.3.3.9 applies schwartzBruhat_acyclic on the norm-one subgroup.

local notation "TI" => InductiveTensor P (SchwartzBruhat K)
local notation "TP" => ProjectiveTensor P (SchwartzBruhat K)
local notation "compareTensors" => @Completion.map TI _ TP _ id

include hSC hm hInt hne hτ

/-- Paper: Proposition D.3.3.10, p. 807. The continuous linear comparison from the
completed inductive tensor product to the completed projective tensor product is bijective
and identifies their bounded subsets. -/
theorem modulatedExponentialDecay_tensor_comparison_bounded :
    ∃ C : Completion TI →L[ℂ] Completion TP, (C : Completion TI → Completion TP) = compareTensors ∧
      Bijective C ∧ ∀ B : Set (Completion TI), IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B :=
  by sorry

/-- Paper: Proposition D.3.3.10, p. 807. The reversed ordering of the completed
inductive tensor factors gives the same quotient stage, with multiplication in split coordinates. -/
theorem modulatedExponentialDecay_stage_tensor_equiv_swap (k : GoodCompact) :
    let k₁ := k.val.comap (Subgroup.subtype K)
    let Tₖ := InductiveTensor P (SchwartzBruhat (K ⧸ k₁))
    ∃ e : Completion Tₖ ≃L[ℂ] ModulatedExponentialDecayStage m I k,
      ∀ (f : P) (h : SchwartzBruhat (K ⧸ k₁)) (u : K) (t : ℝ≥0ˣ),
        (e (Completion.coe' (α := Tₖ) (f ⊗ₜ[ℂ] h))).val
          (((u : G) * τ t : G) : G ⧸ k.val) = h (u : K ⧸ k₁) * f.val (Real.log (t.val : ℝ)) :=
  by sorry

/-- Paper: Proposition D.3.3.10(1), p. 807. A bounded subset of the inductive
decay space is separable and metrizable in the subspace topology. -/
theorem modulatedExponentialDecay_bounded_separable_metrizable
    (B : Set E) (hB : IsVonNBounded ℂ B) : SeparableSpace B ∧ MetrizableSpace B := by sorry

/-- Paper: Proposition D.3.3.10(2), p. 807. The weighted profiles are
continuous for the inductive topology, which is therefore at least as fine
as the topology induced by the family of twists. -/
theorem modulatedExponentialDecay_twists_continuous :
    Continuous (fun (f : E) (a : I) ↦ modulatedExponentialDecayTwist m I a f) := by sorry

-- TODO(paper-gap): The author flags the proof of D.3.3.10(2) as incomplete
-- in footnote 21 on p. 810, including the missing contact with the decay stages.

/-- Paper: Proposition D.3.3.10(2), p. 807. The inductive topology and the
topology induced by the product of the twists have the same bounded sets. -/
theorem modulatedExponentialDecay_bounded_iff_projective (B : Set E) :
    IsVonNBounded ℂ B ↔
      @IsVonNBounded ℂ E _ _ _
        (TopologicalSpace.induced (fun (f : E) (a : I) ↦ modulatedExponentialDecayTwist m I a f)
          inferInstance) B := by sorry

/-- Paper: Proposition D.3.3.10(3), p. 807. A set of decay functions is
bounded exactly when every weighted image is Schwartz–Bruhat bounded. -/
theorem modulatedExponentialDecay_bounded_iff_twists (B : Set E) :
    IsVonNBounded ℂ B ↔
      ∀ a : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B) := by sorry

-- TODO(paper-gap): Accumulation at an included endpoint does not control
-- the twist at that endpoint. The countable testing statement includes it.

/-- Paper: Proposition D.3.3.10(3), p. 807. Boundedness can be checked
on a countable subset of exponents reaching both ends of the interval.
Deviation: Every a in I must lie between two test exponents, allowing equality.
This includes finite endpoints when they belong to I and handles unbounded intervals. -/
theorem modulatedExponentialDecay_bounded_iff_countable_twists
    (B : Set E) (J : Set I) (hJ : J.Countable)
    (hEnds : ∀ a : I, (∃ b ∈ J, (b : ℝ) ≤ a) ∧ ∃ c ∈ J, (a : ℝ) ≤ c) :
    IsVonNBounded ℂ B ↔
      ∀ a ∈ J, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B) := by sorry

/-- Paper: Remark D.3.3.11, p. 811. Pullback along the comparison bijection
identifies the topology generated by bounded seminorms on the projective completion
with the completed inductive tensor topology. -/
theorem modulatedExponentialDecay_tensor_bornologification :
    (inferInstance : TopologicalSpace (Completion TI)) =
      TopologicalSpace.induced compareTensors
        (inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms (Completion TP)
          (Subtype.val : {p : Seminorm ℂ (Completion TP) //
            ∀ B : Set (Completion TP), IsVonNBounded ℂ B → BddAbove (p '' B)} → _)))) :=
  by sorry

/-- Paper: Remark D.3.3.11, p. 811. The comparison between the completed
tensor products is a topological isomorphism exactly when the norm-one dual
is compactly generated. -/
theorem modulatedExponentialDecay_tensor_comparison_homeomorph_iff :
    IsHomeomorph compareTensors ↔ IsCompactlyGeneratedGroup (PontryaginDual K) := by sorry

end BoundedSets

section Isotypes

-- TODO(paper-gap): The proof on p. 812 invokes a closed embedding for the
-- product of twists, although the topology is defined by the inductive stages
-- and Theorem D.3.3.7(4) identifies it with the projective topology for compact I.

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hms : Surjective m) (hInt : OrdConnected I) (hne : I.Nonempty)

include hSC hm hms hInt hne in
/-- Paper: Proposition D.3.3.12, p. 811. Left translation defines a jointly
continuous action of G by continuous linear operators on the decay space. -/
theorem exists_modulatedExponentialDecay_translationAction :
    ∃ ρ : G →* (E →L[ℂ] E),
      (∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x)) ∧
      Continuous (fun p : G × E ↦ ρ p.1 p.2) := by sorry

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (ρ : G →* (ModulatedExponentialDecay m I →L[ℂ] ModulatedExponentialDecay m I))
variable (hρ : ∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x))
variable (ω : PontryaginDual m.toMonoidHom.ker)

local notation "Eω" => actionIsotype (ρ.comp (Subgroup.subtype K)) ω
local notation "Φ" => schwartzBruhatIsotypicProjector m hm μ₁ ω

include hm hms hInt hne hρ

/-- Paper: Proposition D.3.3.12, p. 812. Twisting restricts to a continuous
linear map between the isotypes for the same compact-kernel character. -/
theorem modulatedExponentialDecay_isotype_twist (a : I) :
    let Sω := actionIsotype
      ((schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)) ω
    ∃ T : Eω →L[ℂ] Sω,
      ∀ f, (T f : SchwartzBruhat G) = modulatedExponentialDecayTwist m I a (f : E) := by sorry

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the given isotype
is the unique linear map that commutes with every twist and its ordinary
Schwartz–Bruhat projector.
Deviation: The commuting square is checked in the ambient Schwartz–Bruhat space. -/
theorem existsUnique_modulatedExponentialDecay_isotypicProjector :
    ∃! Q : E →ₗ[ℂ] Eω, ∀ (f : E) (a : I),
      modulatedExponentialDecayTwist m I a (Q f : E) =
        Φ (modulatedExponentialDecayTwist m I a f) := by sorry

variable (Q : ModulatedExponentialDecay m I →ₗ[ℂ]
  actionIsotype (ρ.comp m.toMonoidHom.ker.subtype) ω)
variable (hQ : ∀ (f : ModulatedExponentialDecay m I) (a : I),
  modulatedExponentialDecayTwist m I a (Q f : ModulatedExponentialDecay m I) =
    schwartzBruhatIsotypicProjector m hm μ₁ ω (modulatedExponentialDecayTwist m I a f))

include hQ

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the isotype is continuous. -/
theorem modulatedExponentialDecay_isotypicProjector_continuous : Continuous Q := by sorry

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the isotype is a
retraction of its inclusion, hence a surjective projector. -/
theorem modulatedExponentialDecay_isotypicProjector_retract (f : Eω) : Q (f : E) = f := by sorry

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the isotype is open
for the subspace topology on the isotype. -/
theorem modulatedExponentialDecay_isotypicProjector_open : IsOpenMap Q := by sorry

end Isotypes

section FourierMellin

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

local notation "ΩI" => relativeVerticalStrip m.toMonoidHom (And.left hm) (And.right hm) I

variable [MeasurableSpace G] [hBorel : BorelSpace G]
variable (μ : Measure G) [hHaar : μ.IsHaarMeasure]
variable (hOpen : IsOpen I) (hms : Surjective m)

/-- Paper: Theorem D.3.3.13, p. 812. The Fourier–Mellin integral
uses the quasi-character itself as the multiplier.
Deviation: The formula takes an unbundled function and is extended by zero
outside the relative strip. The convergence statement uses the decay space. -/
def modulatedFourierMellin (f : G → ℂ) (c : QuasiCharacter G) : ℂ :=
  Set.indicator ΩI (fun c ↦ ∫ g, f g * c g ∂μ) c

/-- Paper: Theorem D.3.3.13, p. 812. At the trivial quasi-character the
Fourier–Mellin integral gives the integral of the original function.
Deviation: This is the sanity check at abscissa zero. -/
theorem modulatedFourierMellin_one (f : E) (h0 : (1 : QuasiCharacter G) ∈ ΩI) :
    modulatedFourierMellin m I hm μ f.val 1 = ∫ g, f.val g ∂μ := by
  unfold modulatedFourierMellin
  rw [Set.indicator_of_mem h0]
  simp

include hSC hBorel hHaar hInt hne hOpen

include hms in
/-- Paper: Theorem D.3.3.13, p. 812. The Fourier–Mellin integrand is
absolutely integrable at every quasi-character in the strip. -/
theorem modulatedFourierMellin_integrable (f : E) (c : ΩI) :
    Integrable (fun g ↦ f.val g * (c : QuasiCharacter G) g) μ := by sorry

include hms in
/-- Paper: Theorem D.3.3.13, p. 812. The integral is holomorphic on the
relative strip for the norm-twist atlas of §3.1.1. -/
theorem modulatedFourierMellin_holomorphic (f : E) :
    letI := quasiCharacterChartedSpace m.toMonoidHom
      (hasNormTwistCharts_of_proper m.toMonoidHom hm.1 hm.2)
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (modulatedFourierMellin m I hm μ f.val) ΩI := by sorry

include hms in
/-- Paper: Theorem D.3.3.13, p. 812. The values on the relative strip depend
linearly on the test function.
Deviation: Holomorphy of the range is stated in modulatedFourierMellin_holomorphic. -/
theorem modulatedFourierMellin_linear :
    ∃ M : E →ₗ[ℂ] (ΩI → ℂ), ∀ f c, M f c = modulatedFourierMellin m I hm μ f.val c := by sorry

/-- Paper: Theorem D.3.3.13, p. 812. Left translating a test function
multiplies its transform at c by c(g). -/
theorem modulatedFourierMellin_equivariant (g : G) (f : E) (c : ΩI) :
    let f' : E := ⟨fun x ↦ f.val (g⁻¹ * x),
      modulatedExponentialDecaySubmodule_translate m I hm hms g f⟩
    modulatedFourierMellin m I hm μ f'.val c =
      (c : QuasiCharacter G) g * modulatedFourierMellin m I hm μ f.val c := by
  intro f'
  unfold modulatedFourierMellin
  rw [Set.indicator_of_mem c.property, Set.indicator_of_mem c.property]
  have h1 : ∀ x, f.val (g⁻¹ * x) * (c : QuasiCharacter G) x =
      (c : QuasiCharacter G) g * (f.val (g⁻¹ * x) * (c : QuasiCharacter G) (g⁻¹ * x)) := by
    intro x
    have : (c : QuasiCharacter G) x = (c : QuasiCharacter G) g * (c : QuasiCharacter G) (g⁻¹ * x) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [this]; ring
  show ∫ x, f.val (g⁻¹ * x) * (c : QuasiCharacter G) x ∂μ = _
  simp_rw [h1]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self (fun x ↦ f.val x * (c : QuasiCharacter G) x) g⁻¹

include hms in
/-- Paper: Theorem D.3.3.13, p. 815. The values on the strip determine
the test function. -/
theorem modulatedFourierMellin_injective :
    Injective (fun (f : E) (c : ΩI) ↦ modulatedFourierMellin m I hm μ f.val c) := by sorry

-- TODO(paper-gap): The proof on pp. 813–814 evaluates the scalar profile at τ(t)
-- and later replaces the scalar decay factor with the ordinary Schwartz space.
-- TODO(paper-gap): The tensor formula with probability Haar on K and the scalar
-- Mellin transform requires compatible Haar normalization on G.

include hτ in
/-- Paper: Theorem D.3.3.13, p. 812. In split coordinates the transform is the
completed tensor of compact Fourier transform with frequency inversion and
the scalar Fourier–Mellin transform, followed by the componentwise Schwartz–Bergman evaluations.
Deviation: The tensor identity assumes the product normalization used on
p. 813. -/
theorem modulatedFourierMellin_tensor
    (μ₁ : Measure K) [μ₁.IsHaarMeasure] (hμ₁ : μ₁ univ = 1)
    (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    (e : Completion (InductiveTensor (SchwartzBruhat K) P) ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) P) (h ⊗ₜ[ℂ] f))).val
        ((u : G) * τ t) = h u * f.val (Real.log (t.val : ℝ))) :
    let T := InductiveTensor (SchwartzBruhat K) P
    let U := InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)
    let C := Complex.re ⁻¹' I
    ∃ (F₁ : SchwartzBruhat K ≃L[ℂ] SchwartzBruhat (PontryaginDual K))
      (F : Completion T ≃L[ℂ] Completion U)
      (j : Completion U →L[ℂ] (PontryaginDual K → SchwartzBergman I)),
      (∀ h ω, F₁ h ω = lcaFourier μ₁ h ω⁻¹) ∧
      (∀ (h : SchwartzBruhat K) (f : P),
        F (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f)) =
          Completion.coe' (α := U) (F₁ h ⊗ₜ[ℂ] positiveRealFourierMellin I hOpen hInt hne f)) ∧
      Injective j ∧
      (∀ (H : SchwartzBruhat (PontryaginDual K)) (A : SchwartzBergman I) (ω : PontryaginDual K),
        j (Completion.coe' (α := U) (H ⊗ₜ[ℂ] A)) ω = H ω • A) ∧
      ∀ (z : Completion T) (c : ΩI) (ω : PontryaginDual K) (s : C),
        (∀ (u : K) (t : ℝ≥0ˣ),
          (c : QuasiCharacter G) ((u : G) * τ t) = (ω u : ℂ) * ((t.val : ℝ) : ℂ) ^ (s : ℂ)) →
        modulatedFourierMellin m I hm μ (e z).val c = (j (F z) ω).val s := by sorry

end FourierMellin

end RiemannMasullo
