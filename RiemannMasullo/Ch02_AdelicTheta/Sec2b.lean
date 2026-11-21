module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle

/-!
# Directional derivatives and homogeneous adelic theta functions

Masullo, §§2.2.4–2.2.5, pp. 86–98.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped ContDiff Manifold NNReal NumberField.AdeleRing

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

/-- In mixed real and complex coordinates, the archimedean Schwartz–Bruhat functions
are precisely the classical Schwartz functions on the underlying real vector space. -/
theorem mem_archimedeanSchwartzBruhat_iff (g : InfiniteAdeleRing F → ℂ) :
    g ∘ Multiplicative.toAdd ∈ schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F)) ↔
      ∃ G : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ, ∀ x, G (mixed x) = g x := by
  sorry

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

/-- Paper: Lemma 2.2.4.2, p. 87. Formation of the directional derivative
is continuous in the Schwartz–Bruhat topology. -/
theorem adeleDirectionalDeriv_continuous : Continuous (adeleDirectionalDeriv γ) := by sorry

/-- Paper: Lemma 2.2.4.2, p. 87. The difference quotient in the positive real
parameter converges to the directional derivative at every adele. -/
theorem adeleDirectionalDeriv_tendsto (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (f (Multiplicative.ofAdd ((γ t).val * x)) - f (Multiplicative.ofAdd x)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 (adeleDirectionalDeriv γ f (Multiplicative.ofAdd x))) :=
  by sorry

-- TODO(paper-gap): The last sentence of the proof of Lemma 2.2.4.2 uses
-- injectivity of γ∞. Lemma 2.2.4.1 only gives factorization through the infinite ideles.
-- TODO(paper-gap): The proof of Lemma 2.2.4.3 cites “Lemma ??” for closedness
-- of the section image and invokes the unrestricted bound from Lemma 2.2.2.1(3).

/-- Paper: Lemma 2.2.4.3, p. 88. The difference quotient of theta along the
projected one-parameter subgroup converges to theta of the directional derivative.
The limit is continuous since it is a global theta function. -/
theorem adelicTheta_directionalDeriv (f : ℬ[F]) (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (adelicTheta f (classOf (γ t) * g) - adelicTheta f g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adelicTheta (adeleDirectionalDeriv γ f) g)) := by sorry

end DirectionalDerivatives

section PolarHyperplanes

/-- Paper: Definition 2.2.4.4, p. 91. The evaluations of a test function and
its Fourier transform at zero are complex linear. -/
theorem adelePolarValues_isLinear :
    IsLinearMap ℂ (fun f : ℬ[F] ↦ (f zeroAdele, adeleSchwartzFourier f zeroAdele)) := by sorry

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

/-- Paper: Definition 2.2.4.4, p. 91. Both polar functionals are continuous,
expressed as continuity of the pair of evaluations. -/
theorem adelePolarValues_continuous : Continuous (adelePolarValues (F := F)) := by sorry

variable (γ : ℝ≥0ˣ →ₜ* 𝕀[F])

/-- Paper: Lemma 2.2.4.5(1), p. 91. The common polar kernel is closed in
the Schwartz–Bruhat topology. -/
theorem adelePolarSubspace_closed : IsClosed (adelePolarSubspace F : Set ℬ[F]) := by sorry

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
