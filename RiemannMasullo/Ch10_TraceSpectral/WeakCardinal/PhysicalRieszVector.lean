module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import Mathlib.Tactic

/-! Recover a weighted physical vector from the unweighted bilinear duality pairing. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set Complex NumberField
open scoped InnerProductSpace ComplexConjugate ENNReal NumberField.AdeleRing

namespace RiemannMasullo.WeakCardinal

/-- The canonical orthogonal section sends a quotient Riesz vector to the Riesz
vector of the pullback of the same functional. -/
theorem quotientSection_riesz_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (N : Submodule ℂ E) [IsClosed (N : Set E)]
    (f : StrongDual ℂ (E ⧸ N)) (v : E) :
    ⟪(N.quotientEquivOrthogonal ((InnerProductSpace.toDual ℂ (E ⧸ N)).symm f)).val,v⟫_ℂ =
      f (N.mkQL v) := by
  let q := (InnerProductSpace.toDual ℂ (E ⧸ N)).symm f
  let p := N.quotientEquivOrthogonal (N.mkQL v)
  have hq : N.mkQL p.val = N.mkQL v :=
    (N.quotientEquivOrthogonal_symm_eq_mk p.val p.property).symm.trans
      (N.quotientEquivOrthogonal.symm_apply_apply _)
  have hm : v-p.val ∈ N := (Submodule.Quotient.eq N).mp hq.symm
  have ho := (N.mem_orthogonal' _).mp (N.quotientEquivOrthogonal q).property _ hm
  rw [inner_sub_right] at ho
  calc
    _ = ⟪(N.quotientEquivOrthogonal q).val,p.val⟫_ℂ := sub_eq_zero.mp ho
    _ = ⟪q,N.mkQL v⟫_ℂ := rfl
    _ = _ := InnerProductSpace.toDual_symm_apply

/-- An unweighted integral against the reciprocal-weight representative `J` has
strong Riesz representative `conj J / ρ`, almost everywhere in the original measure. -/
theorem weightedRiesz_ae_of_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ : X → ℝ) (hm : Measurable ρ) (hp : ∀ x, 0 < ρ x)
    (J : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)⁻¹))
    (v : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)))
    (hpair : ∀ u : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)),
      ⟪v,u⟫_ℂ = ∫ x, u x*J x ∂μ) :
    (v : X → ℂ) =ᵐ[μ] fun x ↦ conj (J x)/(ρ x : ℂ) := by
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (ρ x))
  let ν' := μ.withDensity (fun x ↦ ENNReal.ofReal (ρ x)⁻¹)
  have hbase : μ ≪ ν := withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  have hbase' : μ ≪ ν' := withDensity_absolutelyContinuous' hm.inv.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hp x))).ne')
  have hν : ν ≪ μ := withDensity_absolutelyContinuous _ _
  let V (x : X) := conj (J x)/(ρ x : ℂ)
  have hV : AEStronglyMeasurable V ν := by
    simp only [V,div_eq_mul_inv,← Complex.ofReal_inv]
    exact (Complex.continuous_conj.comp_aestronglyMeasurable
      (((Lp.aestronglyMeasurable J).mono_ac hbase').mono_ac hν)).mul
        (Complex.measurable_ofReal.comp hm.inv).aestronglyMeasurable
  have hj : Integrable (fun x ↦ ‖J x‖^2) ν' :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable J)).mp (Lp.memLp J)
  have hi := (integrable_withDensity_iff hm.inv.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hj
  change Integrable (fun x ↦ ‖J x‖^2*(ENNReal.ofReal (ρ x)⁻¹).toReal) μ at hi
  have hVmem : MemLp V 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm hV).mpr
    apply (integrable_withDensity_iff hm.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    refine hi.congr (.of_forall fun x ↦ ?_)
    dsimp only [V]
    simp only [norm_div,norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp x),
      ENNReal.toReal_ofReal (hp x).le,ENNReal.toReal_ofReal (inv_pos.mpr (hp x)).le]
    field_simp [(hp x).ne']
  let U := hVmem.toLp V
  have hU : (U : X → ℂ) =ᵐ[μ] V := hbase.ae_eq hVmem.coeFn_toLp
  have heq : v = U := by
    apply ext_inner_right ℂ
    intro u
    rw [hpair,L2.inner_def,integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (hU.mono fun x hx ↦ ?_)
    change u x*J x = (ENNReal.ofReal (ρ x)).toReal • ⟪U x,u x⟫_ℂ
    rw [hx,ENNReal.toReal_ofReal (hp x).le,Complex.real_smul,RCLike.inner_apply]
    simp only [V,map_div₀,starRingEnd_self_apply,Complex.conj_ofReal]
    field_simp [(Complex.ofReal_ne_zero.mpr (hp x).ne')]
  exact heq ▸ hU

section Native

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F

/-- Physical representative of the section of the Riesz dual of any quotient
functional. The dual embedding is the actual Chapter 10 embedding. -/
theorem spectralSection_riesz_coeFn (a l r s : ℝ) (hI : l ≤ r) (hs : 0 ≤ s)
    (f : StrongDual ℂ (spectralSobolevQuotient F a hI hs)) :
    (((globalThetaSobolev F a hI hs).quotientEquivOrthogonal
      ((InnerProductSpace.toDual ℂ (spectralSobolevQuotient F a hI hs)).symm f)).val : C𝔽 → ℂ)
      =ᵐ[μ𝔽] fun g ↦ conj ((spectralSobolevDualEmbedding F a hI hs f) g) /
        (intervalSobolevDensity l r s (logIdeleClassNorm F g) : ℂ) := by
  let N := globalThetaSobolev F a hI hs
  let J := spectralSobolevDualEmbedding F a hI hs f
  let ρ (g : C𝔽) := intervalSobolevDensity l r s (logIdeleClassNorm F g)
  have hlog : Measurable (logIdeleClassNorm F) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hρc : Continuous (intervalSobolevDensity l r s) := by
    unfold intervalSobolevDensity
    exact (by fun_prop : Continuous (fun x : ℝ ↦ max (Real.exp (2*l*x)) (Real.exp (2*r*x)))).mul
      ((by fun_prop : Continuous (fun x : ℝ ↦ 1+x^2)).rpow_const (fun x ↦ Or.inl (by dsimp; positivity)))
  have hρ : Measurable ρ := hρc.measurable.comp hlog
  have hp (g : C𝔽) : 0 < ρ g := mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
    (Real.rpow_pos_of_pos (by positivity) _)
  apply weightedRiesz_ae_of_pairing μ𝔽 ρ hρ hp J
  intro u
  exact (quotientSection_riesz_inner N f u).trans ((spectralSobolevPairing_dual hI hs
    (f.comp N.mkQL) u).2)

end Native

end RiemannMasullo.WeakCardinal
