module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle

/-!
# Directional derivatives and homogeneous adelic theta functions

Masullo, §§2.2.4–2.2.5, pp. 86–98.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped ContDiff Manifold NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "N₁[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "valueℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)
local notation "normℝ" => fun (g : C[F]) ↦ valueℝ (ideleClassNorm F g)
local notation "expUnit" => fun s : ℝ ↦ Homeomorph.symm (Nonneg.unitsHomeomorphPos ℝ) (Real.expOrderIso s)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

section DirectionalDerivatives

variable (γ : ℝ≥0ˣ →ₜ* 𝕀[F])

/-- Paper: Lemma 2.2.4.1, p. 87. Every idele in a continuous one-parameter
subgroup has finite component one. -/
theorem adeleOneParameter_finite_eq_one (t : ℝ≥0ˣ) : (γ t).val.2 = 1 := by
  have : ConnectedSpace ℝ≥0ˣ :=
    (Nonneg.unitsHomeomorphPos ℝ).connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp (isConnected_Ioi (a := (0 : ℝ))))
  have hVal : Continuous (fun s : ℝ≥0ˣ ↦ (γ s).val) :=
    Units.continuous_val.comp γ.continuous
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro v
  have hCoord : Continuous (fun s : ℝ≥0ˣ ↦ (γ s).val.2 v) :=
    (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp hVal)
  calc
    (γ t).val.2 v = (γ 1).val.2 v :=
      TotallyDisconnectedSpace.eq_of_continuous _ hCoord t 1
    _ = (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v := by rw [map_one]; rfl

/-- Paper: Lemma 2.2.4.1, p. 87. The norm of a continuous one-parameter
subgroup is a power of its positive real parameter, with unique real exponent.
The norm-one case has exponent zero. -/
theorem adeleOneParameter_norm_rpow :
    ∃! α : ℝ, ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α := by
  let E : ℝ ≃ₜ ℝ≥0ˣ :=
    Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hE (x : ℝ) : valueℝ (E x) = Real.exp x := rfl
  have hEadd (x y : ℝ) : E (x + y) = E x * E y :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add x y))
  have hpos (t : ℝ≥0ˣ) : 0 < valueℝ t := NNReal.coe_pos.mpr (Units.zero_lt t)
  let f : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun x ↦ Real.log (valueℝ (ideleNorm F (γ (E x))))) (by
      intro x y
      dsimp only
      rw [hEadd, map_mul, map_mul, Units.val_mul, NNReal.coe_mul,
        Real.log_mul (hpos _).ne' (hpos _).ne'])
  have hf : Continuous f := by
    change Continuous (fun x ↦ Real.log (valueℝ (ideleNorm F (γ (E x)))))
    have hNorm : Continuous (ideleNorm F) := (ideleGroup_topology F).2.2.2.2.1
    exact (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (hNorm.comp (γ.continuous.comp E.continuous)))).log
      fun x ↦ (hpos _).ne'
  have hlinear (x : ℝ) : f x = x * f 1 := by
    simpa only [smul_eq_mul, mul_one] using map_real_smul f hf x (1 : ℝ)
  have hpower (x a : ℝ) : (valueℝ (E x)) ^ a = Real.exp (x * a) := by
    rw [hE, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  have h (t : ℝ≥0ˣ) : valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ f 1 := by
    obtain ⟨x, rfl⟩ := E.surjective t
    rw [hpower, ← hlinear]
    exact (Real.exp_log (hpos _)).symm
  refine ⟨f 1, h, fun a ha ↦ ?_⟩
  have ha' := (ha (E 1)).symm.trans (h (E 1))
  simpa only [hpower, one_mul, Real.exp_eq_exp] using ha'

/-- Paper: Lemma 2.2.4.1(1)–(2), p. 87. The norm of the subgroup is either
an automorphism smooth in both directions or identically one. Smoothness is
expressed in the logarithmic coordinate on the positive reals. -/
theorem adeleOneParameter_norm_cases :
    Xor
      (∃ e : ℝ≥0ˣ ≃ₜ* ℝ≥0ˣ, (∀ t, e t = ideleNorm F (γ t)) ∧
        ContDiff ℝ (∞ : ℕ∞ω) (fun s : ℝ ↦ Real.log (valueℝ (e (expUnit s)))) ∧
        ContDiff ℝ (∞ : ℕ∞ω) (fun s : ℝ ↦ Real.log (valueℝ (e.symm (expUnit s)))))
      (∀ t : ℝ≥0ˣ, ideleNorm F (γ t) = 1) := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let n : ℝ≥0ˣ →* ℝ≥0ˣ := (ideleNorm F).comp γ.toMonoidHom
  have hE (s : ℝ) : valueℝ (E s) = Real.exp s := rfl
  have hLog (t : ℝ≥0ˣ) : Real.log (valueℝ t) = E.symm t := by
    obtain ⟨s, rfl⟩ := E.surjective t
    rw [hE, Real.log_exp, E.symm_apply_apply]
  have hZero : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hAdd (s t : ℝ) : E (s + t) = E s * E t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add s t))
  -- In logarithmic coordinates, the norm is a continuous additive map on ℝ.
  let f : ℝ →+ ℝ := AddMonoidHom.mk' (fun s ↦ E.symm (n (E s))) (by
    intro s t
    apply E.injective
    simp only [E.apply_symm_apply, hAdd, map_mul])
  have hf : Continuous f := E.symm.continuous.comp
    ((ideleGroup_topology F).2.2.2.2.1.comp (γ.continuous.comp E.continuous))
  let α := f 1
  have hNorm (s : ℝ) : n (E s) = E (α * s) := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change f s = f 1 * s
    simpa only [smul_eq_mul, mul_one, mul_comm s (f 1)] using map_real_smul f hf s (1 : ℝ)
  by_cases hα : α = 0
  · have hn (t : ℝ≥0ˣ) : n t = 1 := by
      obtain ⟨s, rfl⟩ := E.surjective t
      rw [hNorm, hα, zero_mul, hZero]
    refine Or.inr ⟨hn, ?_⟩
    rintro ⟨e, he, -, -⟩
    have heOne (t : ℝ≥0ˣ) : e t = 1 := (he t).trans (hn t)
    exact one_ne_zero (E.injective (e.injective ((heOne (E 1)).trans (heOne (E 0)).symm)))
  · let H := (E.symm.trans (Homeomorph.mulLeft₀ α hα)).trans E
    have hH (t : ℝ≥0ˣ) : H t = n t := by
      change E (α * E.symm t) = n t
      rw [← hNorm, E.apply_symm_apply]
    let e := ContinuousMulEquiv.mk' H (by
      intro t u
      simp only [hH, map_mul])
    refine Or.inl ⟨⟨e, hH, ?_, ?_⟩, ?_⟩
    · change ContDiff ℝ (∞ : ℕ∞ω) (fun s ↦ Real.log (valueℝ (E (α * E.symm (E s)))))
      simp only [hLog, E.symm_apply_apply]
      exact contDiff_const.mul contDiff_id
    · change ContDiff ℝ (∞ : ℕ∞ω) (fun s ↦ Real.log (valueℝ (E (α⁻¹ * E.symm (E s)))))
      simp only [hLog, E.symm_apply_apply]
      exact contDiff_const.mul contDiff_id
    · intro hn
      have hOne : E α = 1 := by
        simpa only [mul_one] using (hNorm 1).symm.trans (hn (E 1))
      exact hα (E.injective (hOne.trans hZero.symm))

local notation "orbitDeriv" => fun (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (f : ℬ[F]) (x : Multiplicative 𝔸[F]) ↦
  deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd (Units.val (γ (expUnit s)) * Multiplicative.toAdd x))) 0

section Archimedean

open scoped Classical

local notation "mixed" => InfiniteAdeleRing.ringEquiv_mixedSpace F

/-- Euclidean coordinates identify the full, trivial-kernel Bruhat stage with the
classical Schwartz space. Every structural stage maps into this stage. -/
private theorem mem_schwartzBruhatSubmodule_euclidean_iff
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] {n : ℕ}
    (v : A ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n))) (g : A → ℂ) :
    g ∈ schwartzBruhatSubmodule A ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, s (v x).toAdd = g x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let P := ElementaryLieGroup n 0 0 PUnit
  let D := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit
  let : Unique D := uniqueOfSubsingleton 0
  let p : Multiplicative E ≃ₜ* Multiplicative P :=
    { toMulEquiv := (AddEquiv.prodUnique (M := E) (N := D)).symm.toMultiplicative
      continuous_toFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : E ↦ (x, (default : D))))
      continuous_invFun := (continuous_fst : Continuous (Prod.fst : E × D → E)) }
  let e : ElementaryLCAPresentation A :=
    { realDim := n, torusDim := 0, latticeRank := 0, finiteFactor := PUnit, equiv := v.trans p }
  have hA := (lca_elementary_iff (G := A)).mpr ⟨e⟩
  let i : (⊤ : Subgroup A) ≃ₜ* A :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair A := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hA.1,
    isBruhatGoodSubgroup_bot_iff.mpr hA.2, bot_le⟩
  let q₀ : A →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hq₀ : IsOpenQuotientMap q₀ :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have hinj : Injective q₀ := (MonoidHom.ker_eq_bot_iff q₀).mp (eq_bot_iff.mpr fun x hx ↦ by
    exact (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective q₀ ⟨hinj, hq₀.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hq₀.isQuotientMap.isOpen_preimage)
  let e₀ : ElementaryLCAPresentation a.quotient := { e with equiv := q.symm.trans e.equiv }
  have hreal (s : SchwartzBruhatStage e₀) (x : A) :
      schwartzBruhatStageRealization a e₀ s x = s ((v x).toAdd, 0, 0, PUnit.unit) := by
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    change s ((e₀.equiv (q x)).toAdd) = _
    change s ((e.equiv (q.symm (q x))).toAdd) = _
    rw [q.symm_apply_apply]
    rfl
  have hrange : schwartzBruhatSubmodule A = (schwartzBruhatStageRealization a e₀).range := by
    refine le_antisymm (iSup_le fun b ↦ iSup_le fun eb ↦ ?_) ?_
    · rintro _ ⟨sb, rfl⟩
      obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (show b ≤ a from ⟨le_top, le_top⟩) eb e₀
      exact ⟨j sb, hj sb⟩
    · exact le_iSup_of_le a (le_iSup (fun e ↦ (schwartzBruhatStageRealization a e).range) e₀)
  rw [hrange, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    let f : E → ℂ := fun x ↦ s (x, 0, 0, PUnit.unit)
    have hs' (y : P) : f y.1 = s y :=
      congrArg (fun z : P ↦ s z) (Prod.ext rfl (Subsingleton.elim _ _))
    have hf : (fun y : P ↦ f y.1) ∈ elementarySchwartzSubmodule n 0 0 PUnit :=
      (funext hs').symm ▸ s.property
    obtain ⟨S, hS⟩ := (elementarySchwartzSubmodule_real_iff f).mp hf
    refine ⟨S, fun x ↦ ?_⟩
    exact (congrFun hS (v x).toAdd).trans
      ((hreal s x).symm.trans (congrFun hs x))
  · rintro ⟨s, hs⟩
    let t : SchwartzBruhatStage e₀ :=
      ⟨fun y : P ↦ s y.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨s, rfl⟩⟩
    exact ⟨t, funext fun x ↦ (hreal t x).trans (hs x)⟩

omit [NumberField F] in
/-- The mixed coordinate map on infinite adeles is continuous in both directions. -/
private theorem continuous_mixedCoordinates : Continuous mixed ∧ Continuous (mixed).symm := by
  classical
  open InfinitePlace in
  let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd IsReal (fun v : InfinitePlace F ↦ v.Completion)).trans
      ((Homeomorph.piCongrRight fun v ↦
          (Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
        ((Homeomorph.piCongrRight fun v ↦
          (Completion.isometryEquivComplexOfIsComplex
            (not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex))))
  exact ⟨h.continuous, h.symm.continuous⟩

/-- In mixed real and complex coordinates, the archimedean Schwartz–Bruhat functions
are precisely the classical Schwartz functions on the underlying real vector space. -/
theorem mem_archimedeanSchwartzBruhat_iff (g : InfiniteAdeleRing F → ℂ) :
    g ∘ Multiplicative.toAdd ∈ schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F)) ↔
      ∃ G : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ, ∀ x, G (mixed x) = g x := by
  classical
  let V := mixedEmbedding.mixedSpace F
  let n := Module.finrank ℝ V
  let L : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  obtain ⟨hm, hm'⟩ := continuous_mixedCoordinates (F := F)
  let v : Multiplicative (InfiniteAdeleRing F) ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n)) :=
    { toMulEquiv := ((mixed).toAddEquiv.trans L.toLinearEquiv.toAddEquiv).toMultiplicative
      continuous_toFun := L.continuous.comp hm
      continuous_invFun := hm'.comp L.symm.continuous }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) :=
    v.toHomeomorph.isEmbedding.t2Space
  rw [mem_schwartzBruhatSubmodule_euclidean_iff v]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L s, fun x ↦ hs (Multiplicative.ofAdd x)⟩
  · rintro ⟨s, hs⟩
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm s, fun x ↦ ?_⟩
    change s (L.symm (L (mixed x.toAdd))) = g x.toAdd
    rw [L.symm_apply_apply, hs]

/-- The logarithmically parametrized archimedean component of the subgroup is
differentiable at the identity in mixed coordinates. -/
private theorem adeleOneParameter_archimedean_differentiable :
    DifferentiableAt ℝ (fun s : ℝ ↦ mixed (γ (expUnit s)).val.1) 0 := by
  have hCharacter (c : ℝ≥0ˣ →ₜ* ℂ) : DifferentiableAt ℝ (fun s ↦ c (expUnit s)) 0 := by
    obtain ⟨z, hz, _⟩ := existsUnique_complexPower c
    have hExp (s : ℝ) : c (expUnit s) = Complex.exp ((s : ℂ) * z) := by
      have h := hz (expUnit s)
      change c (expUnit s) = (↑(Real.exp s) : ℂ) ^ z at h
      refine h.trans ?_
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
        ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp]
    simp_rw [hExp]
    exact Complex.differentiableAt_exp.comp 0
      (Complex.ofRealCLM.differentiableAt.mul_const z)
  have hc (v : InfinitePlace F) :
      DifferentiableAt ℝ (fun s : ℝ ↦
        InfinitePlace.Completion.extensionEmbedding v ((γ (expUnit s)).val.1 v)) 0 := by
    let c : ℝ≥0ˣ →ₜ* ℂ :=
      { toFun := fun t ↦ InfinitePlace.Completion.extensionEmbedding v ((γ t).val.1 v)
        map_one' := by rw [map_one]; exact map_one _
        map_mul' := fun t u ↦ by rw [map_mul]; exact map_mul _ _ _
        continuous_toFun := (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
          ((continuous_apply v).comp (continuous_fst.comp (Units.continuous_val.comp γ.continuous))) }
    exact hCharacter c
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply DifferentiableAt.prodMk
  · refine differentiableAt_pi.mpr fun v ↦ ?_
    have h := Complex.reCLM.differentiableAt.comp 0 (hc v.1)
    have hReal (s : ℝ) : (InfinitePlace.Completion.extensionEmbedding v.1
        ((γ (expUnit s)).val.1 v.1)).re =
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 ((γ (expUnit s)).val.1 v.1) := by
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply v.2, Complex.ofReal_re]
    change DifferentiableAt ℝ (fun s ↦ (InfinitePlace.Completion.extensionEmbedding v.1
      ((γ (expUnit s)).val.1 v.1)).re) 0 at h
    simpa only [hReal] using h
  · exact differentiableAt_pi.mpr fun v ↦ hc v.1

/-- Differentiating a pure archimedean test function along the logarithmic
dilation gives an archimedean test function, with an actual pointwise derivative. -/
private theorem adeleDirectionalDeriv_archimedean
    (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) :
    ∃ d : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)), ∀ x : InfiniteAdeleRing F,
      HasDerivAt (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x)))
        (d (Multiplicative.ofAdd x)) 0 := by
  let V := mixedEmbedding.mixedSpace F
  obtain ⟨G, hG⟩ := (mem_archimedeanSchwartzBruhat_iff
    (fun x ↦ f (Multiplicative.ofAdd x))).mp f.property
  let curve : ℝ → V := fun s ↦ mixed (γ (expUnit s)).val.1
  let velocity : V := deriv curve 0
  have hCurve : HasDerivAt curve velocity 0 :=
    (adeleOneParameter_archimedean_differentiable γ).hasDerivAt
  have hOne : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hZero : curve 0 = 1 := by
    have hγ : γ (expUnit (0 : ℝ)) = 1 := (congrArg γ hOne).trans (map_one γ)
    exact (congrArg (fun u : 𝕀[F] ↦ mixed u.val.1) hγ).trans (map_one mixed)
  let L : V →L[ℝ] V := ContinuousLinearMap.mul ℝ V velocity
  let D : SchwartzMap V ℂ :=
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ).flip L.hasTemperateGrowth
      (SchwartzMap.fderivCLM ℝ V ℂ G)
  have hmem := (mem_archimedeanSchwartzBruhat_iff (fun x ↦ D (mixed x))).mpr ⟨D, fun _ ↦ rfl⟩
  refine ⟨⟨fun x ↦ D (mixed x.toAdd), hmem⟩, fun x ↦ ?_⟩
  have hOrbit : HasDerivAt (fun s ↦ curve s * mixed x) (L (mixed x)) 0 :=
    hCurve.mul_const (mixed x)
  have hG' : HasFDerivAt G (fderiv ℝ G (mixed x)) (curve 0 * mixed x) := by
    rw [hZero, one_mul]
    exact G.hasFDerivAt _
  have hEval : (fun s : ℝ ↦ G (curve s * mixed x)) =
      fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x)) := by
    funext s
    rw [← hG, map_mul mixed]
  rw [← hEval]
  exact hG'.comp_hasDerivAt 0 hOrbit

end Archimedean

open scoped TensorProduct in
/-- Paper: Lemma 2.2.4.2, p. 87. Differentiating the orbit curve pointwise in
the logarithmic parameter gives a Schwartz–Bruhat function. -/
theorem adeleDirectionalDeriv_mem (f : ℬ[F]) :
    orbitDeriv γ f ∈ schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by
  obtain ⟨e, he⟩ := adeleSchwartz_inductiveTensor_equiv F
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B := SchwartzBruhat (Multiplicative (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  let E : (A ⊗[ℂ] B) ≃ₗ[ℂ] ℬ[F] := e.toLinearEquiv
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq (E.symm f)
  have hf : f = ∑ i, E (a i ⊗ₜ[ℂ] b i) := by
    calc
      f = E (E.symm f) := (E.apply_symm_apply f).symm
      _ = E (∑ i, a i ⊗ₜ[ℂ] b i) := congrArg E hab
      _ = _ := map_sum E _ _
  choose d hd using fun i ↦ adeleDirectionalDeriv_archimedean γ (a i)
  let eval (x : 𝔸[F]) : ℬ[F] →ₗ[ℂ] ℂ :=
    { toFun := fun g ↦ g (Multiplicative.ofAdd x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let g (i : Fin n) : ℬ[F] := E (a i ⊗ₜ[ℂ] b i)
  let dg (i : Fin n) : ℬ[F] := E (d i ⊗ₜ[ℂ] b i)
  have hDeriv (i : Fin n) (x : 𝔸[F]) :
      HasDerivAt (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x) (g i)) (eval x (dg i)) 0 := by
    let aOrbit (s : ℝ) := a i (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1))
    let bValue := b i (Multiplicative.ofAdd x.2)
    have hEval : (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x) (g i)) =
        fun s : ℝ ↦ aOrbit s * bValue := by
      funext s
      refine (he (a i) (b i) ((γ (expUnit s)).val * x)).trans ?_
      have hFinite : ((γ (expUnit s)).val.2 * x.2) = x.2 :=
        (congrArg (· * x.2) (adeleOneParameter_finite_eq_one γ (expUnit s))).trans (one_mul _)
      exact congrArg (fun y ↦ aOrbit s * b i (Multiplicative.ofAdd y)) hFinite
    have hValue : eval x (dg i) = d i (Multiplicative.ofAdd x.1) * bValue := he (d i) (b i) x
    exact (congrArg₂ (fun c v ↦ HasDerivAt c v (0 : ℝ)) hEval hValue).mpr
      ((hd i x.1).mul_const bValue)
  let result : ℬ[F] := ∑ i, dg i
  have hEq : orbitDeriv γ f = (result : Multiplicative 𝔸[F] → ℂ) := by
    funext x
    have hOrbit : (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x.toAdd) f) =
        fun s : ℝ ↦ ∑ i, eval ((γ (expUnit s)).val * x.toAdd) (g i) := by
      funext s
      let ev := eval ((γ (expUnit s)).val * x.toAdd)
      exact (congrArg ev hf).trans (map_sum ev g Finset.univ)
    have hValue : eval x.toAdd result = ∑ i, eval x.toAdd (dg i) :=
      map_sum (eval x.toAdd) dg Finset.univ
    change deriv (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x.toAdd) f) 0 = eval x.toAdd result
    exact (congrArg (fun c ↦ deriv c 0) hOrbit).trans
      ((HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hDeriv i x.toAdd).deriv.trans hValue.symm)
  rw [hEq]
  exact result.property

/-- Paper: Lemma 2.2.4.2, p. 87. The Archimedean coordinates of a continuous
one-parameter group of ideles are differentiable in the logarithmic parameter. -/
private theorem adeleOneParameter_infinite_differentiableAt :
    DifferentiableAt ℝ
      (fun s : ℝ ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F (γ (expUnit s)).val.1) 0 := by
  classical
  have hScalar {𝕜 : Type} [RCLike 𝕜] (g : ℝ → 𝕜) (hg : Continuous g)
      (hOne : g 0 = 1) (hMul : ∀ s t, g (s + t) = g s * g t) :
      DifferentiableAt ℝ g 0 := by
    -- A nonzero interval integral expresses the subgroup curve through its primitive.
    let I : ℝ → 𝕜 := fun t ↦ ∫ u in 0..t, g u
    have hI t : HasDerivAt I (g t) t :=
      intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    obtain ⟨b, hb⟩ : ∃ b, I b ≠ 0 := by
      by_contra! hz
      exact one_ne_zero <| hOne.symm.trans <| (hI 0).deriv.symm.trans <| by
        simp [show I = 0 from funext hz]
    have hEq (s : ℝ) : g s = (I (s + b) - I s) / I b := by
      rw [eq_div_iff hb, eq_sub_iff_add_eq']
      dsimp only [I]
      rw [← intervalIntegral.integral_const_mul]
      simp only [← hMul, intervalIntegral.integral_comp_add_left, add_zero]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    rw [show g = _ from funext hEq]
    exact (((hI (0 + b)).differentiableAt.comp (0 : ℝ) (differentiableAt_id.add_const b)).sub
      (hI 0).differentiableAt).div_const (I b)
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let a : ℝ → InfiniteAdeleRing F := fun s ↦ (γ (E s)).val.1
  have hExpAdd (s t : ℝ) : E (s + t) = E s * E t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add s t))
  have ha : Continuous a :=
    continuous_fst.comp (Units.continuous_val.comp (γ.continuous.comp E.continuous))
  have haZero : a 0 = 1 := by
    have hExpZero : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
    change (γ (E 0)).val.1 = 1
    rw [hExpZero, map_one]
    rfl
  have haAdd (s t : ℝ) : a (s + t) = a s * a t := by
    show (γ (E (s + t))).val.1 = _
    rw [hExpAdd, map_mul]
    rfl
  let b (s : ℝ) (v : {v : InfinitePlace F // v.IsReal}) :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (a s v)
  let c (s : ℝ) (v : {v : InfinitePlace F // v.IsComplex}) :=
    InfinitePlace.Completion.extensionEmbedding v.1 (a s v)
  have hb : DifferentiableAt ℝ b 0 := differentiableAt_pi.mpr fun v ↦
    hScalar _ ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      ((continuous_apply v.1).comp ha)) (by
        show InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (a 0 v) = 1
        rw [haZero]
        exact map_one _) (fun s t ↦ by
        show InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (a (s + t) v) = _
        rw [haAdd]
        exact map_mul _ _ _)
  have hc : DifferentiableAt ℝ c 0 := differentiableAt_pi.mpr fun v ↦
    hScalar _ ((InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      ((continuous_apply v.1).comp ha)) (by
        show InfinitePlace.Completion.extensionEmbedding v.1 (a 0 v) = 1
        rw [haZero]
        exact map_one _) (fun s t ↦ by
        show InfinitePlace.Completion.extensionEmbedding v.1 (a (s + t) v) = _
        rw [haAdd]
        exact map_mul _ _ _)
  exact hb.prodMk hc

/-- Pulling a Schwartz–Bruhat function back along a translate of a continuous
homomorphism from a real normed vector space gives a differentiable function. -/
private theorem schwartzBruhat_differentiableAt_comp_translate
    {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Multiplicative E →ₜ* G) (f : SchwartzBruhat G) (x : G) (z : E) :
    DifferentiableAt ℝ (fun y : E ↦ f (x * i (Multiplicative.ofAdd y))) z := by
  classical
  let v : E → G := fun y ↦ x * i (Multiplicative.ofAdd y)
  let fs : schwartzBruhatSubmodule G := f
  change DifferentiableAt ℝ (fs.val ∘ v) z
  refine Submodule.iSup_induction (motive := fun g : G → ℂ ↦
    DifferentiableAt ℝ (g ∘ v) z) _
    fs.property (fun a g hg ↦ ?_) (differentiableAt_const _) (fun _ _ hg hh ↦ hg.add hh)
  refine Submodule.iSup_induction (motive := fun g : G → ℂ ↦
    DifferentiableAt ℝ (g ∘ v) z) _ hg
    (fun e g ⟨s, hs⟩ ↦ ?_) (differentiableAt_const _) (fun _ _ hg hh ↦ hg.add hh)
  subst g
  let U : OpenSubgroup G := ⟨a.val.1, a.property.1⟩
  have hi : Continuous (fun y : E ↦ i (Multiplicative.ofAdd y)) := i.continuous
  have hiMem (y : Multiplicative E) : i y ∈ U :=
    (isPreconnected_range hi).subset_isClopen U.isClopen
      ⟨1, ⟨0, map_one i⟩, U.one_mem⟩ (mem_range_self y.toAdd)
  by_cases hx : x ∈ U
  · let iU : Multiplicative E →* a.val.1 :=
      i.toMonoidHom.codRestrict a.val.1 hiMem
    let q : a.val.1 →* a.quotient := QuotientGroup.mk' _
    let c : E →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
      AddMonoidHom.toMultiplicative.symm (e.equiv.toMulEquiv.toMonoidHom.comp (q.comp iU))
    have hc : Continuous c :=
      e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (i.continuous.subtype_mk hiMem))
    let cR := (AddMonoidHom.fst _ _).comp c
    let cT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp c)
    let L := cR.toRealLinearMap hc.fst
    have hD (y : E) : (c y).2.2 = 0 :=
      (hc.snd.snd.isConst_of_preconnectedSpace y 0).trans (by rw [map_zero]; rfl)
    have hLift (j : Fin e.torusDim) :
        ∃ l : E →L[ℝ] ℝ, ∀ y, (l y : AddCircle (1 : ℝ)) = (c y).2.1 j := by
      let χ := (Pi.evalAddMonoidHom _ j).comp cT
      have hχ : Continuous χ := (continuous_apply j).comp hc.snd.fst
      exact exists_addCircle_coe_linearMap_eq χ hχ
    choose l hl using hLift
    let W := EuclideanSpace ℝ (Fin e.torusDim)
    let M : E →L[ℝ] W :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e.torusDim ↦ ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi l)
    let y₀ := (e.equiv (q ⟨x, hx⟩)).toAdd
    obtain ⟨w, hw⟩ := elementaryCover_surjective y₀.2.2.1 y₀.2.2.2 y₀.1 y₀.2.1
    have hCover (y : E) :
        elementaryCover (y₀.1 + L y, w + M y) y₀.2.2.1 y₀.2.2.2 = y₀ + c y := by
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · funext j
        have hwj := congrArg (fun r : ElementaryLieGroup e.realDim e.torusDim e.latticeRank
          e.finiteFactor ↦ r.2.1 j) hw
        change ((w j + l j y : ℝ) : AddCircle (1 : ℝ)) = y₀.2.1 j + (c y).2.1 j
        rw [AddCircle.coe_add, show (w j : AddCircle (1 : ℝ)) = y₀.2.1 j from hwj, hl]
      · change y₀.2.2 = y₀.2.2 + (c y).2.2
        rw [hD, add_zero]
    let ss : elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor := s
    have hs : Differentiable ℝ (fun b ↦ s (elementaryCover b y₀.2.2.1 y₀.2.2.2)) :=
      (ss.property.1 _ _).differentiable (by simp)
    have hp : Differentiable ℝ (fun y : E ↦ (y₀.1 + L y, w + M y)) :=
      (L.differentiable.const_add _).prodMk (M.differentiable.const_add _)
    convert (hs.comp hp) z using 1
    funext y
    have hyU : v y ∈ a.val.1 := U.mul_mem hx (hiMem (Multiplicative.ofAdd y))
    rw [Function.comp_apply, schwartzBruhatStageRealization_apply, dite_eq_left hyU]
    apply congrArg (fun r ↦ s r)
    rw [hCover]
    change (e.equiv (q (⟨v y, hyU⟩ : a.val.1))).toAdd =
      (e.equiv (q (⟨x, hx⟩ : a.val.1)) * e.equiv (q (iU (Multiplicative.ofAdd y)))).toAdd
    rw [← map_mul, ← map_mul]
    exact congrArg (fun j : a.val.1 ↦ (e.equiv (q j)).toAdd) (Subtype.ext rfl)
  · have hn (y : E) : v y ∉ U := fun hy ↦ hx (by
      have h := U.mul_mem hy (U.inv_mem (hiMem (Multiplicative.ofAdd y)))
      simpa [v] using h)
    convert (differentiableAt_const (x := z) (c := (0 : ℂ))) using 1
    funext y
    exact (schwartzBruhatStageRealization_apply a e s (v y)).trans (dite_eq_right (hn y))

/-- Paper: Lemma 2.2.4.2, p. 87. An adelic Schwartz–Bruhat function is
differentiable in the Archimedean coordinates at each fixed finite adele. -/
private theorem adeleSchwartz_infinite_differentiableAt (f : ℬ[F])
    (x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    DifferentiableAt ℝ (fun a : mixedEmbedding.mixedSpace F ↦
      f (Multiplicative.ofAdd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, x))) z := by
  classical
  let E := mixedEmbedding.mixedSpace F
  let eArch := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hInv : Continuous eArch.symm := by
    apply continuous_pi
    intro v
    rcases v.isReal_or_isComplex with hv | hv
    · exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
        ((continuous_apply ⟨v, hv⟩).comp continuous_fst)).congr fun y ↦ by
          apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
          exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).apply_symm_apply
            (y.1 ⟨v, hv⟩)).trans
              (congrFun (congrArg Prod.fst (eArch.apply_symm_apply y)).symm ⟨v, hv⟩)
    · exact ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous.comp
        ((continuous_apply ⟨v, hv⟩).comp continuous_snd)).congr fun y ↦ by
          apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).injective
          exact ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).apply_symm_apply
            (y.2 ⟨v, hv⟩)).trans
              (congrFun (congrArg Prod.snd (eArch.apply_symm_apply y)).symm ⟨v, hv⟩)
  let i : E →+ 𝔸[F] := eArch.symm.toAddMonoidHom.prod (0 : E →+ _)
  have hi : Continuous i := hInv.prodMk continuous_const
  let j : Multiplicative E →ₜ* Multiplicative 𝔸[F] := ⟨i.toMultiplicative, hi⟩
  have h := schwartzBruhat_differentiableAt_comp_translate j f
    (Multiplicative.ofAdd (0, x)) z
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  exact congrArg (fun p : 𝔸[F] ↦ f (Multiplicative.ofAdd p))
    (Prod.ext (zero_add _).symm (add_zero _).symm)

/-- Paper: Lemma 2.2.4.2, p. 87. The logarithmic dilation orbit of a
Schwartz–Bruhat function has a derivative at zero. -/
private theorem adeleOrbit_differentiableAt (f : ℬ[F]) (x : Multiplicative 𝔸[F]) :
    DifferentiableAt ℝ
      (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val * x.toAdd))) 0 := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let a : ℝ → mixedEmbedding.mixedSpace F := fun s ↦ e (γ (expUnit s)).val.1 * e x.toAdd.1
  have hγ := adeleOneParameter_infinite_differentiableAt γ
  have hb : DifferentiableAt ℝ (fun s : ℝ ↦ (a s).1) 0 := differentiableAt_pi.mpr fun v ↦
    (differentiableAt_pi.mp hγ.fst v).mul_const _
  have hc : DifferentiableAt ℝ (fun s : ℝ ↦ (a s).2) 0 := differentiableAt_pi.mpr fun v ↦
    (differentiableAt_pi.mp hγ.snd v).mul_const _
  have ha : DifferentiableAt ℝ a 0 := hb.prodMk hc
  have h := (adeleSchwartz_infinite_differentiableAt f x.toAdd.2 (a 0)).comp (0 : ℝ) ha
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  let b := (γ (expUnit s)).val.1
  let c := (γ (expUnit s)).val.2
  have hArch : b * x.toAdd.1 = e.symm (a s) := by
    change _ = e.symm (e b * e x.toAdd.1)
    rw [← e.map_mul, e.symm_apply_apply]
  have hFin : c * x.toAdd.2 = x.toAdd.2 :=
    (congrArg (· * x.toAdd.2) (adeleOneParameter_finite_eq_one γ (expUnit s))).trans (one_mul _)
  exact congrArg (fun y : 𝔸[F] ↦ f (Multiplicative.ofAdd y)) (Prod.ext hArch hFin)

/-- Paper: Lemma 2.2.4.2, p. 87. Formation of the directional derivative is
complex linear on the adelic Schwartz–Bruhat space. -/
theorem adeleDirectionalDeriv_isLinear :
    IsLinearMap ℂ (fun f : ℬ[F] ↦
      (⟨orbitDeriv γ f, adeleDirectionalDeriv_mem γ f⟩ : ℬ[F])) := by
  constructor
  · intro f g
    apply Subtype.ext
    funext x
    exact deriv_add (adeleOrbit_differentiableAt γ f x) (adeleOrbit_differentiableAt γ g x)
  · intro c f
    apply Subtype.ext
    funext x
    exact deriv_fun_const_smul_field c _

/-- Paper: Equation (2.2.4.2), p. 87. The directional derivative differentiates
`f (γ(t) x)` at `t = 1` and is a complex-linear endomorphism.
Deviation: The definition uses the equivalent parameter `t = exp s` at `s = 0`,
as in (2.2.4.4). -/
def adeleDirectionalDeriv : ℬ[F] →ₗ[ℂ] ℬ[F] :=
  IsLinearMap.mk' _ (adeleDirectionalDeriv_isLinear γ)

/-- Paper: Lemma 2.2.4.2, pp. 87–88. Differentiation of the archimedean orbit
in the logarithmic parameter is a continuous complex-linear operator on
archimedean Schwartz–Bruhat functions. -/
theorem exists_archimedeanDirectionalDeriv :
    ∃ D : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) →L[ℂ]
        SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)),
      ∀ (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) (x : InfiniteAdeleRing F),
        D f (Multiplicative.ofAdd x) =
          deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x))) 0 := by
  sorry

/-- Tensoring a continuous endomorphism with the identity is continuous for
the inductive tensor topology. -/
private theorem continuous_inductiveTensorMap_id {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] (L : A →L[ℂ] A) :
    Continuous (inductiveTensorMap L.toLinearMap (LinearMap.id (M := B))) := by
  let T := inductiveTensorMap L.toLinearMap (LinearMap.id (M := B))
  let hS := withGeneratingSeminorms_spec (A ⊗[ℂ] B)
    (fun p : {p : Seminorm ℂ (A ⊗[ℂ] B) //
      (∀ f : A, Continuous (fun g : B ↦ p (f ⊗ₜ[ℂ] g))) ∧
      (∀ g : B, Continuous (fun f : A ↦ p (f ⊗ₜ[ℂ] g)))} ↦ p.val)
  refine hS.continuous_of_continuous_comp T fun p ↦ ?_
  exact hS.continuous_seminorm
    ⟨p.val.comp T, fun f ↦ p.property.1 (L f), fun g ↦ (p.property.2 g).comp L.continuous⟩

/-- Paper: Lemma 2.2.4.2, p. 87. Formation of the directional derivative
is continuous in the Schwartz–Bruhat topology. -/
theorem adeleDirectionalDeriv_continuous : Continuous (adeleDirectionalDeriv γ) := by
  refine Exists.elim (adeleSchwartz_inductiveTensor_equiv F) fun e he ↦ ?_
  refine Exists.elim (exists_archimedeanDirectionalDeriv γ) fun D hD ↦ ?_
  let I := ContinuousLinearMap.id ℂ (SchwartzBruhat (Multiplicative 𝔸ᶠ[F]))
  let T := inductiveTensorMap D.toLinearMap I.toLinearMap
  have hleft : (adeleDirectionalDeriv γ).comp e.toLinearEquiv.toLinearMap =
      e.toLinearEquiv.toLinearMap.comp T := by
    apply TensorProduct.ext'
    intro f g
    apply Subtype.ext
    funext y
    let x := Multiplicative.toAdd y
    have hOrbit (s : ℝ) :
        e (f ⊗ₜ[ℂ] g)
            (Multiplicative.ofAdd ((γ (expUnit s)).val * x)) =
          f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1)) *
            g (Multiplicative.ofAdd x.2) := by
      have hfinite : ((γ (expUnit s)).val * x).2 = x.2 := by
        change (γ (expUnit s)).val.2 * x.2 = x.2
        rw [adeleOneParameter_finite_eq_one γ (expUnit s), one_mul]
      exact (he f g _).trans (congrArg (fun z : 𝔸ᶠ[F] ↦
        f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1)) *
          g (Multiplicative.ofAdd z)) hfinite)
    change deriv (fun s : ℝ ↦ e (f ⊗ₜ[ℂ] g)
      (Multiplicative.ofAdd ((γ (expUnit s)).val * x))) 0 =
        e (D f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x)
    let u (s : ℝ) := f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1))
    let v := g (Multiplicative.ofAdd x.2)
    exact (congrArg (fun k : ℝ → ℂ ↦ deriv k 0) (funext hOrbit)).trans
      ((deriv_mul_const_field (u := u) v).trans
        ((congrArg (· * v) (hD f x.1).symm).trans (he (D f) g x).symm))
  have hcont : Continuous T :=
    continuous_inductiveTensorMap_id (B := SchwartzBruhat (Multiplicative 𝔸ᶠ[F])) D
  refine (e.continuous.comp (hcont.comp e.symm.continuous)).congr fun f ↦ ?_
  change e (T (e.symm f)) = adeleDirectionalDeriv γ f
  have h := DFunLike.congr_fun hleft (e.symm f)
  change adeleDirectionalDeriv γ (e (e.symm f)) = e (T (e.symm f)) at h
  simpa only [e.apply_symm_apply] using h.symm

/-- Paper: Lemma 2.2.4.2, p. 87. The difference quotient in the positive real
parameter converges to the directional derivative at every adele. -/
theorem adeleDirectionalDeriv_tendsto (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (f (Multiplicative.ofAdd ((γ t).val * x)) - f (Multiplicative.ofAdd x)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 (adeleDirectionalDeriv γ f (Multiplicative.ofAdd x))) := by
  have hOrbit := (adeleOrbit_differentiableAt γ f (Multiplicative.ofAdd x)).hasDerivAt
  have hLog := hOrbit.scomp_of_eq (1 : ℝ) (Real.hasDerivAt_log one_ne_zero) Real.log_one.symm
  rw [inv_one, one_smul] at hLog
  have hVal : Tendsto valueℝ (𝓝[≠] (1 : ℝ≥0ˣ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc := NNReal.continuous_coe.comp (Units.continuous_val (M := ℝ≥0))
      exact (hc.continuousAt (x := (1 : ℝ≥0ˣ))).continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he ↦ ht (Units.val_injective (NNReal.coe_injective he))
  refine (hLog.tendsto_slope.comp hVal).congr' (Eventually.of_forall fun t ↦ ?_)
  have hExpLog : expUnit (Real.log (valueℝ t)) = t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
  have hZero : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  simp only [Function.comp_apply, slope_def_module, Real.log_one, hExpLog, hZero,
    map_one, Units.val_one, one_mul, toAdd_ofAdd, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_sub, Complex.ofReal_one, div_eq_inv_mul]

-- TODO(paper-gap): The last sentence of the proof of Lemma 2.2.4.2 uses
-- injectivity of γ∞. Lemma 2.2.4.1 only gives factorization through the infinite ideles.
-- TODO(paper-gap): The proof of Lemma 2.2.4.3 cites “Lemma ??” for closedness
-- of the section image and invokes the unrestricted bound from Lemma 2.2.2.1(3).

/-- If a Schwartz–Bruhat function represents the pointwise logarithmic orbit derivative,
its theta series gives the derivative of the original theta series. -/
private theorem adelicTheta_tendsto_of_orbitDeriv (f d : ℬ[F])
    (hd : ∀ x : Multiplicative 𝔸[F],
      HasDerivAt (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val * x.toAdd))) (d x) 0)
    (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (adelicTheta f (classOf (γ t) * g) - adelicTheta f g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adelicTheta d g)) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  let E : ℝ → ℝ≥0ˣ := expUnit
  have hE : Continuous E :=
    (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous
  have hZero : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hAdd (s t : ℝ) : E (s + t) = E s * E t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add s t))
  let x (ξ : Fˣ) (s : ℝ) : 𝔸[F] := (γ (E s) * a).val * algebraMap F 𝔸[F] (ξ : F)
  let term (φ : ℬ[F]) (ξ : Fˣ) (s : ℝ) := φ (Multiplicative.ofAdd (x ξ s))
  have hDeriv (ξ : Fˣ) (s : ℝ) : HasDerivAt (term f ξ) (term d ξ s) s := by
    have h : HasDerivAt
        (fun t : ℝ ↦ f (Multiplicative.ofAdd ((γ (E t)).val * x ξ s)))
        (term d ξ s) (s - s) := by
      simpa only [sub_self, toAdd_ofAdd] using hd (Multiplicative.ofAdd (x ξ s))
    refine (h.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
    change f (Multiplicative.ofAdd (x ξ t)) =
      f (Multiplicative.ofAdd ((γ (E (t - s))).val * x ξ s))
    have hMul : γ (E t) = γ (E (t - s)) * γ (E s) := by
      rw [← map_mul γ, ← hAdd, sub_add_cancel]
    simp only [x, hMul, Units.val_mul, mul_assoc]
  let p (s : ℝ) : 𝕀[F] × 𝔸[F] := (γ (E s) * a, 0)
  have hp : Continuous p :=
    ((γ.continuous.comp hE).mul continuous_const).prodMk continuous_const
  let K := p '' Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hp
  have hAbs (φ : ℬ[F]) := adelicAverage_summableUniformlyOn φ K hK
  have hUniform : TendstoUniformlyOn (fun S s ↦ ∑ ξ ∈ S, term d ξ s)
      (fun s ↦ ∑' ξ, term d ξ s) atTop (Ioo (-1 : ℝ) 1) := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hAbs d).hasSumUniformlyOn.tendstoUniformlyOn ε hε] with S hS s hs
    have hmem : p s ∈ K := mem_image_of_mem p (Ioo_subset_Icc_self hs)
    have hsum : Summable (fun ξ ↦ ‖term d ξ s‖) := by
      simpa only [term, x, p, add_zero] using (hAbs d).summable hmem
    have htail := hS (p s) hmem
    simp only [p, add_zero] at htail
    change dist (∑' ξ, ‖term d ξ s‖) (∑ ξ ∈ S, ‖term d ξ s‖) < ε at htail
    rw [dist_eq_norm, ← hsum.sum_add_tsum_subtype_compl S, add_sub_cancel_left,
      Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)] at htail
    rw [dist_eq_norm, ← hsum.of_norm.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
    exact (norm_tsum_le_tsum_norm (hsum.subtype fun ξ ↦ ξ ∉ S)).trans_lt htail
  have hSeries : HasDerivAt (fun s ↦ ∑' ξ, term f ξ s) (∑' ξ, term d ξ 0) 0 := by
    refine hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hUniform
      (Eventually.of_forall fun S s _ ↦ HasDerivAt.fun_sum fun ξ _ ↦ hDeriv ξ s) ?_ (by simp)
    intro s hs
    have hmem : p s ∈ K := mem_image_of_mem p (Ioo_subset_Icc_self hs)
    have hsum : Summable (fun ξ ↦ ‖term f ξ s‖) := by
      simpa only [term, x, p, add_zero] using (hAbs f).summable hmem
    exact hsum.of_norm.hasSum
  have hTheta (φ : ℬ[F]) (s : ℝ) :
      (∑' ξ, term φ ξ s) = adelicTheta φ (classOf (γ (E s)) * classOf a) := by
    rw [← QuotientGroup.mk_mul, adelicTheta_mk]
    simp only [term, x, mul_comm]
  have hThetaZero (φ : ℬ[F]) : (∑' ξ, term φ ξ 0) = adelicTheta φ (classOf a) := by
    rw [hTheta, ← QuotientGroup.mk_mul, hZero, map_one, one_mul]
  have hLog := hSeries.scomp_of_eq (1 : ℝ) (Real.hasDerivAt_log one_ne_zero) Real.log_one.symm
  rw [inv_one, one_smul, hThetaZero] at hLog
  have hVal : Tendsto valueℝ (𝓝[≠] (1 : ℝ≥0ˣ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc := NNReal.continuous_coe.comp (Units.continuous_val (M := ℝ≥0))
      exact (hc.continuousAt (x := (1 : ℝ≥0ˣ))).continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he ↦ ht (Units.val_injective (NNReal.coe_injective he))
  refine (hLog.tendsto_slope.comp hVal).congr' (Eventually.of_forall fun t ↦ ?_)
  have hExpLog : E (Real.log (valueℝ t)) = t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
  rw [Function.comp_apply, slope_def_module, Function.comp_apply, Function.comp_apply,
    Real.log_one, hThetaZero, hTheta, hExpLog]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    div_eq_inv_mul]

/-- Paper: Lemma 2.2.4.3, p. 88. The difference quotient of theta along the
projected one-parameter subgroup converges to theta of the directional derivative.
The limit is continuous since it is a global theta function. -/
theorem adelicTheta_directionalDeriv (f : ℬ[F]) (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (adelicTheta f (classOf (γ t) * g) - adelicTheta f g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adelicTheta (adeleDirectionalDeriv γ f) g)) := by
  exact adelicTheta_tendsto_of_orbitDeriv γ f (adeleDirectionalDeriv γ f)
    (fun x ↦ (adeleOrbit_differentiableAt γ f x).hasDerivAt) g

end DirectionalDerivatives

section PolarHyperplanes

/-- Paper: Definition 2.2.4.4, p. 91. The evaluations of a test function and
its Fourier transform at zero are complex linear. -/
theorem adelePolarValues_isLinear :
    IsLinearMap ℂ (fun f : ℬ[F] ↦ (f zeroAdele, adeleSchwartzFourier f zeroAdele)) := by
  constructor
  · intro f g
    refine Prod.ext rfl ?_
    simp only [(adeleSchwartzFourier_apply_zero _).2]
    exact integral_add (adeleSchwartzFourier_apply_zero f).1
      (adeleSchwartzFourier_apply_zero g).1
  · intro c f
    refine Prod.ext rfl ?_
    simp only [(adeleSchwartzFourier_apply_zero _).2]
    exact integral_smul c (fun x ↦ f (Multiplicative.ofAdd x))

/-- Paper: Definition 2.2.4.4, p. 91. The two polar functionals are the
coordinates of the map that evaluates a test function and its transform at zero. -/
def adelePolarValues : ℬ[F] →ₗ[ℂ] ℂ × ℂ :=
  IsLinearMap.mk' _ (adelePolarValues_isLinear (F := F))

/-- Paper: Definition 2.2.4.4, p. 91. The polar functionals give the test
function and Fourier transform values at zero. -/
theorem adelePolarValues_apply (f : ℬ[F]) :
    adelePolarValues (F := F) f = (f zeroAdele, adeleSchwartzFourier f zeroAdele) := rfl

/-- Paper: Definition 2.2.4.4, p. 91. The intersection of the global polar
hyperplanes is the common kernel of the two polar functionals. -/
def adelePolarSubspace (F : Type*) [Field F] [NumberField F] : Submodule ℂ ℬ[F] :=
  LinearMap.ker (adelePolarValues (F := F))

/-- Paper: Definition 2.2.4.4, p. 91. A function belongs to the polar
subspace exactly when both it and its Fourier transform vanish at zero. -/
theorem mem_adelePolarSubspace (f : ℬ[F]) :
    f ∈ adelePolarSubspace F ↔ f zeroAdele = 0 ∧ adeleSchwartzFourier f zeroAdele = 0 :=
  LinearMap.mem_ker.trans Prod.mk_eq_zero

open scoped ENNReal in
/-- Point evaluation is continuous in the Schwartz–Bruhat topology since its
norm is bounded on each stage by the zeroth Schwartz seminorm. -/
private theorem schwartzBruhat_continuous_eval {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ℝ≥0∞).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f z‖₊ : ℝ≥0∞)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

/-- Integration against regular Haar measure is continuous on the Schwartz–Bruhat
space, since it evaluates the Fourier transform at the trivial character. -/
private theorem schwartzBruhat_continuous_integral {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    Continuous (fun f : SchwartzBruhat G ↦ ∫ x, f x ∂μ) := by
  obtain ⟨Fourier, hFourier⟩ := schwartzBruhat_fourier_equiv μ
  refine ((schwartzBruhat_continuous_eval (1 : PontryaginDual G)).comp Fourier.continuous).congr
    fun f ↦ ?_
  exact ((hFourier f).2 1).trans (lcaFourier_one μ f (hFourier f).1)

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Definition 2.2.4.4, p. 91. Both polar functionals are continuous,
expressed as continuity of the pair of evaluations. -/
theorem adelePolarValues_continuous : Continuous (adelePolarValues (F := F)) := by
  change Continuous (fun f : ℬ[F] ↦ (f zeroAdele, adeleSchwartzFourier f zeroAdele))
  refine (schwartzBruhat_continuous_eval zeroAdele).prodMk ?_
  let G := Multiplicative 𝔸[F]
  let : MeasurableSpace 𝔸[F] := borel _
  let μ : Measure G := additiveTamagawaMeasure F
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  exact (schwartzBruhat_continuous_integral (G := G) μ).congr
    fun f ↦ (adeleSchwartzFourier_apply_zero f).2.symm

variable (γ : ℝ≥0ˣ →ₜ* 𝕀[F])

/-- Paper: Lemma 2.2.4.5(1), p. 91. The common polar kernel is closed in
the Schwartz–Bruhat topology. -/
theorem adelePolarSubspace_closed : IsClosed (adelePolarSubspace F : Set ℬ[F]) := by
  exact isClosed_singleton.preimage (adelePolarValues_continuous (F := F))

/-- Paper: Lemma 2.2.4.5(1), p. 91. Directional differentiation preserves the
common polar kernel, so it induces a linear map on the polar quotient. -/
theorem adeleDirectionalDeriv_preserves_polarSubspace :
    adelePolarSubspace F ≤ (adelePolarSubspace F).comap (adeleDirectionalDeriv γ) := by sorry

/-- Paper: Equation (2.2.4.25), p. 91. The two polar evaluations are jointly
surjective, so they identify the quotient by their common kernel with `ℂ × ℂ`. -/
theorem adelePolarValues_surjective : Surjective (adelePolarValues (F := F)) := by sorry

/-- Paper: Lemma 2.2.4.5(2), p. 91. In the two evaluation coordinates on
the quotient, the induced derivative has diagonal entries `0` and `-α`,
where `α` is the norm exponent of the subgroup. -/
theorem adeleDirectionalDeriv_polarQuotient_diagonal (α : ℝ)
    (hα : ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α) (z : ℂ × ℂ) :
    let T : (ℬ[F] ⧸ adelePolarSubspace F) ≃ₗ[ℂ] ℂ × ℂ :=
      (adelePolarValues (F := F)).quotKerEquivOfSurjective (adelePolarValues_surjective (F := F))
    let D : (ℬ[F] ⧸ adelePolarSubspace F) →ₗ[ℂ] ℬ[F] ⧸ adelePolarSubspace F :=
      (adelePolarSubspace F).mapQ (τ₁₂ := RingHom.id ℂ) (adelePolarSubspace F)
        (adeleDirectionalDeriv (F := F) γ) (adeleDirectionalDeriv_preserves_polarSubspace (F := F) γ)
    T.toFun (D.toFun (T.symm.toFun z)) = (0, (-α) • z.2) := by sorry

local instance adelicThetaAdeleMeasurableSpace : MeasurableSpace 𝔸[F] := borel _

/-- Paper: Lemma 2.2.4.5(3), p. 92. The difference quotient of the Fourier
transform under inverse dilation, weighted by the reciprocal norm, converges
pointwise to the Fourier transform of the directional derivative. -/
theorem adeleDirectionalDeriv_fourier_tendsto (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      ((valueℝ (ideleNorm F (γ t)))⁻¹ •
          adeleSchwartzFourier f (Multiplicative.ofAdd (((γ t)⁻¹).val * x)) -
        adeleSchwartzFourier f (Multiplicative.ofAdd x)) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd x))) :=
  by sorry

/-- Paper: Equation (2.2.4.30), p. 92. The Fourier transform of the derivative
uses the conjugate standard character and the real trace of the archimedean
velocity times the frequency and integration variable. The integrand is integrable.
Deviation: The velocity is expressed using the complex embeddings of the local
completions in the logarithmic parameter. The real trace counts complex places twice. -/
theorem adeleDirectionalDeriv_fourier_integral (f : ℬ[F]) (α : ℝ)
    (hα : ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α) :
    ∃ velocity : InfinitePlace F → ℂ,
      (∀ v, HasDerivAt (fun s : ℝ ↦
        InfinitePlace.Completion.extensionEmbedding v ((γ (expUnit s)).val.1 v))
        (velocity v) 0) ∧
      ∀ x : 𝔸[F],
        let integrand := fun y : 𝔸[F] ↦
          f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F (x * y) : ℂ) *
            (-(α : ℂ) + 2 * Real.pi * Complex.I *
              (∑ v : InfinitePlace F, (v.mult : ℝ) *
                (velocity v * InfinitePlace.Completion.extensionEmbedding v (x.1 v * y.1 v)).re : ℝ))
        Integrable integrand (additiveTamagawaMeasure F) ∧
          adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd x) =
            ∫ y, integrand y ∂additiveTamagawaMeasure F := by sorry

-- TODO(paper-gap): On p. 92 the proof of Lemma 2.2.4.5 incorrectly drops
-- the norm factor at x = 0. The limit is -α * f̂(0), as in part (2).
-- The finite local factors of (2.2.4.32) also evaluate f_v at x_v under dν_v(y_v).

/-- Paper: Remark 2.2.4.6, p. 92. The norm-weighted inverse-dilation
quotients of the Fourier transforms converge in the Schwartz–Bruhat topology,
uniformly over every bounded set of inputs. -/
theorem adeleDirectionalDeriv_fourier_tendstoUniformlyOn (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun (t : ℝ≥0ˣ) (f : ℬ[F]) ↦
      (((valueℝ t : ℂ) - 1)⁻¹) •
        (((valueℝ (ideleNorm F (γ t)) : ℂ)⁻¹) •
          schwartzBruhatUnitTranslate (γ t) (adeleSchwartzFourier f) - adeleSchwartzFourier f))
      (fun f ↦ adeleSchwartzFourier (adeleDirectionalDeriv γ f)) (𝓝[≠] 1) B := by sorry

end PolarHyperplanes

section HomogeneousTheta

local instance adelicThetaIdeleMeasurableSpace : MeasurableSpace 𝕀[F] := borel _
local instance adelicThetaClassMeasurableSpace : MeasurableSpace C[F] := borel _

local notation "χ[" F "]" => PontryaginDual C₁[F]
local notation "μ₁" => normOneIdeleTamagawaMeasure F
local notation "μ̄₁" => normOneIdeleClassTamagawaMeasure F
local notation "classIntegrand" => fun (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) (h : C₁[F]) ↦
  adelicTheta f (Subtype.val h * g) * (ω₁ h : ℂ)

/-- Paper: Definition 2.2.5.1, p. 95. The character-weighted theta integrand
is integrable over the compact group of norm-one idele classes. -/
theorem homogeneousAdelicTheta_integrable (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) :
    Integrable (classIntegrand ω₁ f g) μ̄₁ := by sorry

/-- Paper: Lemma 2.2.5.2(2), p. 95. Averaging theta against the character on
the norm-one idele classes gives a continuous function of the ambient class. -/
theorem homogeneousAdelicTheta_continuous (ω₁ : χ[F]) (f : ℬ[F]) :
    Continuous (fun g ↦ ∫ h, classIntegrand ω₁ f g h ∂μ̄₁) := by sorry

/-- Paper: Definition 2.2.5.1, p. 95. Homogeneous theta is the integral of
theta at `h * g`, weighted by `ω₁ h` against norm-one class Haar measure. -/
def homogeneousAdelicTheta (ω₁ : χ[F]) (f : ℬ[F]) : C(C[F], ℂ) :=
  ⟨fun g ↦ ∫ h, classIntegrand ω₁ f g h ∂μ̄₁, homogeneousAdelicTheta_continuous ω₁ f⟩

/-- Paper: Definition 2.2.5.1, p. 95. For the trivial character and at the
identity class, homogeneous theta integrates theta over the norm-one classes. -/
theorem homogeneousAdelicTheta_trivial_at_one (f : ℬ[F]) :
    homogeneousAdelicTheta (1 : χ[F]) f 1 = ∫ h : C₁[F], adelicTheta f h.val ∂μ̄₁ := by
  simp only [homogeneousAdelicTheta, ContinuousMap.coe_mk]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  refine (congrArg₂ (· * ·) (congrArg (adelicTheta f) (mul_one h.val))
    (congrArg Subtype.val (PontryaginDual.one_apply h))).trans (mul_one _)

/-- Paper: Definition 2.2.5.1, p. 95. Formation of homogeneous theta is
complex linear in the test function. -/
theorem homogeneousAdelicTheta_isLinear (ω₁ : χ[F]) :
    IsLinearMap ℂ (homogeneousAdelicTheta ω₁) := by sorry

local notation "classOfNormOne" => fun h : N₁[F] ↦
  (Subtype.mk (classOf (Subtype.val h)) (Subtype.property h) : C₁[F])
local notation "ideleIntegrand" => fun (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) (h : N₁[F]) ↦
  f (Multiplicative.ofAdd (Units.val (Subtype.val h * g))) * (ω₁ (classOfNormOne h) : ℂ)

/-- Paper: Lemma 2.2.5.2(1), p. 95. The integral of the adelic test function
against the character pulled back from the norm-one classes converges absolutely
on norm-one ideles. -/
theorem homogeneousAdelicTheta_idele_integrable (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) :
    Integrable (ideleIntegrand ω₁ f g) μ₁ := by sorry

/-- Paper: Lemma 2.2.5.2(1), p. 95. The norm-one idele integral against the
pulled-back character is continuous in the ambient idele. -/
theorem homogeneousAdelicTheta_idele_continuous (ω₁ : χ[F]) (f : ℬ[F]) :
    Continuous (fun g ↦ ∫ h, ideleIntegrand ω₁ f g h ∂μ₁) := by sorry

/-- Paper: Lemma 2.2.5.2(1), p. 95. Inverse translation of the ambient
idele by a norm-one idele multiplies the integral by the pulled-back character. -/
theorem homogeneousAdelicTheta_idele_homogeneous (ω₁ : χ[F]) (f : ℬ[F])
    (h₀ : N₁[F]) (g : 𝕀[F]) :
    (∫ h, ideleIntegrand ω₁ f (h₀.val⁻¹ * g) h ∂μ₁) =
      (ω₁ (classOfNormOne h₀) : ℂ) * ∫ h, ideleIntegrand ω₁ f g h ∂μ₁ := by sorry

/-- Paper: Lemma 2.2.5.2(2), p. 95. At an idele representative, homogeneous
theta equals the test-function integral over the norm-one ideles. -/
theorem homogeneousAdelicTheta_eq_idele_integral (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) :
    homogeneousAdelicTheta ω₁ f (classOf g) = ∫ h, ideleIntegrand ω₁ f g h ∂μ₁ := by sorry

-- TODO(paper-gap): The paragraph on p. 96 describes h⁻¹ * g inside (2.2.5.2),
-- while the displayed integral and the equivariance computation on p. 97 use h * g.
-- Bound (2.2.5.5) reuses the unrestricted estimate flagged in §2.2.2.1(3).
-- TODO(later): needs §4.3.3 for the general construction cited by Remark 2.2.5.3.

/-- Paper: Theorem 2.2.5.4(1), p. 97. Inverse translation of a class by a
norm-one class acts on homogeneous theta by the prescribed character. -/
theorem homogeneousAdelicTheta_homogeneous (ω₁ : χ[F]) (f : ℬ[F]) (h : C₁[F]) (g : C[F]) :
    homogeneousAdelicTheta ω₁ f (h.val⁻¹ * g) = (ω₁ h : ℂ) * homogeneousAdelicTheta ω₁ f g :=
  by sorry

/-- Paper: Theorem 2.2.5.4(2), p. 97. At large norm, homogeneous theta decays
faster than every inverse power of the norm. -/
theorem homogeneousAdelicTheta_decay_large (ω₁ : χ[F]) (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < normℝ g →
      ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

open scoped Classical in
/-- Paper: Equation (2.2.5.10), p. 97. The polar term is the norm-one class
volume times the difference of the two polar evaluations with reciprocal norm
on the Fourier value. It contributes only for the trivial character. -/
def homogeneousAdelicTheta_polarTerm (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) : ℂ :=
  if ω₁ = 1 then (μ̄₁ univ).toReal •
    ((normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele) else 0

/-- Paper: Equation (2.2.5.10), p. 97. At norm one and for the trivial
character the polar term is the class volume times the difference of the evaluations. -/
theorem homogeneousAdelicTheta_polarTerm_trivial_at_one (f : ℬ[F]) :
    homogeneousAdelicTheta_polarTerm (1 : χ[F]) f 1 =
      (μ̄₁ univ).toReal • (adeleSchwartzFourier f zeroAdele - f zeroAdele) := by
  simp [homogeneousAdelicTheta_polarTerm]

/-- Paper: Theorem 2.2.5.4(2), p. 97. After subtracting the polar term,
homogeneous theta decays faster than every power of the norm at small norm. -/
theorem homogeneousAdelicTheta_decay_small (ω₁ : χ[F]) (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], normℝ g < T →
      ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
        C * (normℝ g) ^ N := by sorry

/-- Paper: Theorem 2.2.5.4(3), p. 97. Homogeneous theta commutes with
directional differentiation. The difference quotient tends to homogeneous theta
of the differentiated test function. -/
theorem homogeneousAdelicTheta_directionalDeriv (γ : ℝ≥0ˣ →ₜ* 𝕀[F])
    (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (homogeneousAdelicTheta ω₁ f (classOf (γ t) * g) - homogeneousAdelicTheta ω₁ f g) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 (homogeneousAdelicTheta ω₁ (adeleDirectionalDeriv γ f) g)) :=
  by sorry

open scoped Classical in
set_option maxSynthPendingDepth 8 in
/-- Paper: Theorem 2.2.5.4(3), p. 98. With the finite component fixed,
homogeneous theta on ideles is smooth in the archimedean units. The charts
are the units charts in the real and complex completion coordinates. -/
theorem homogeneousAdelicTheta_archimedean_smooth (ω₁ : χ[F]) (f : ℬ[F])
    (g : 𝔸ᶠ[F]ˣ) :
    let e := Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMulEquiv
    ContMDiff 𝓘(ℝ, mixedEmbedding.mixedSpace F) 𝓘(ℝ, ℂ) (∞ : ℕ∞ω)
      (fun a : (mixedEmbedding.mixedSpace F)ˣ ↦
        homogeneousAdelicTheta ω₁ f (classOf
          ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) 𝔸ᶠ[F]).symm
            (e.symm a, g)))) := by sorry

-- TODO(paper-gap): The proof of Theorem 2.2.5.4(3) repeats the same term in
-- (2.2.5.13), then uses γ(t⁻¹) with the sign for γ(t) in (2.2.5.15).

/-- Paper: Theorem 2.2.5.4(4), p. 98. For a test function in the polar
subspace or a nontrivial character, homogeneous theta decays at both ends
at every exponential rate in the absolute logarithmic norm. -/
theorem homogeneousAdelicTheta_decay_both (ω₁ : χ[F]) (f : ℬ[F])
    (h : f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < |Real.log (normℝ g)| →
      ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by sorry

-- TODO(paper-gap): The last sentence of Theorem 2.2.5.4(4) uses the
-- conjugate of ω to descend to the logarithmic norm. Even after choosing a
-- character extension, this transforms by ω(h)⁻² under translation by h.

-- TODO(paper-gap): Theorem 2.2.5.4(5) cites (2.2.5.11) among the estimates
-- with a constant and a threshold, although it is an identity valid everywhere.

/-- Paper: Theorem 2.2.5.4(5), p. 98. The large-norm, small-norm and two-sided
estimates have a common constant and logarithmic threshold uniform over a
bounded set of test functions. The two-sided bound retains the condition in (4). -/
theorem homogeneousAdelicTheta_decay_bounded (ω₁ : χ[F]) (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C[F],
      (T < Real.log (normℝ g) → ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (T < -Real.log (normℝ g) →
        ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
          C * (normℝ g) ^ N) ∧
      ((f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) → T < |Real.log (normℝ g)| →
        ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) :=
  by sorry

/-- Paper: Theorem 2.2.5.4(6), p. 98. The three uniform estimates hold with
logarithmic threshold one and a common constant. -/
theorem homogeneousAdelicTheta_decay_bounded_threshold_one (ω₁ : χ[F]) (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F],
      (1 < Real.log (normℝ g) → ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (1 < -Real.log (normℝ g) →
        ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
          C * (normℝ g) ^ N) ∧
      ((f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) → 1 < |Real.log (normℝ g)| →
        ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) :=
  by sorry

end HomogeneousTheta

end RiemannMasullo
