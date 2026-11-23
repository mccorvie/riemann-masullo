module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.Topology.ContinuousMap.CompactlySupported

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Subspace
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Prod

/-! # Strong continuity and the Hilbert-space isotypic transform -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function MeasureTheory Set TopologicalSpace
open scoped CompactlySupported ENNReal InnerProductSpace NNReal

section Regular

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Paper: Definition 4.3.1.1, p. 175. The space of the regular representation
is complex Haar L².
Deviation: Mathlib's inner product is conjugate-linear in the first slot.
The paper uses the swapped order, as made explicit in `regularL2_inner`. -/
abbrev RegularL2 (ν : Measure G) := Lp ℂ 2 ν

/-- Paper: Definition 4.3.1.1, p. 175. Swapping the arguments of Mathlib's inner
product gives the integral of the first function times the conjugate of the second. -/
theorem regularL2_inner (ν : Measure G) (f h : RegularL2 ν) :
    ⟪h, f⟫_ℂ = ∫ x, f x * star (h x) ∂ν := by
  rfl

variable (ν : Measure G) [hν : ν.IsHaarMeasure]

include hν

/-- Paper: Lemma 4.3.1.3, p. 175. Haar measure is regular. -/
theorem regularL2_haar_regular : ν.Regular := by infer_instance

/-- Paper: Lemma 4.3.1.3, p. 175. Haar measure is Radon, expressed by inner
regularity by compact sets together with finiteness on compact sets. -/
theorem regularL2_haar_radon : ν.InnerRegular ∧ IsFiniteMeasureOnCompacts ν :=
  ⟨inferInstance, inferInstance⟩

/-- Paper: Lemma 4.3.1.3, p. 175. Haar measure on the second-countable group is
sigma-finite. -/
theorem regularL2_haar_sigmaFinite : SigmaFinite ν := by infer_instance

/-- Paper: Remark 4.3.1.4, p. 175. A continuous compactly supported function
is square-integrable. -/
theorem regularL2_memLp_compactlySupported (f : G →C_c ℂ) :
    MemLp (f : G → ℂ) 2 ν := by
  exact f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport

/-- Paper: Remark 4.3.1.4, p. 175. Classes of continuous compactly
supported functions are dense in Haar L². -/
theorem regularL2_compactlySupported_dense :
    DenseRange (fun f : G →C_c ℂ ↦ (regularL2_memLp_compactlySupported ν f).toLp f) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hs, hdist, hc, hg⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε.ne'
  let k : G →C_c ℂ := ⟨⟨g, hc⟩, hs⟩
  refine ⟨hg.toLp g, ⟨k, rfl⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]

/-- Paper: Lemma 4.3.1.5(1), p. 176. The Haar L² space is separable. -/
theorem regularL2_separable : SeparableSpace (RegularL2 ν) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  infer_instance

/-- Paper: Lemma 4.3.1.5(2), p. 176. Left translation on Haar L² is precomposition
with multiplication by the inverse group element, extending the action in (4.3.1.4), p. 175. -/
def regularTranslate (g : G) (f : RegularL2 ν) : RegularL2 ν :=
  DomMulAct.mk g⁻¹ • f

/-- Paper: Lemma 4.3.1.5(2), p. 176. The representative of the L² left translate
agrees almost everywhere with the inverse-translation formula in (4.3.1.4), p. 175. -/
theorem regularTranslate_ae_eq (g : G) (f : RegularL2 ν) :
    (regularTranslate ν g f : G → ℂ) =ᵐ[ν] fun x ↦ f (g⁻¹ * x) := by
  exact DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g⁻¹) f

private theorem regularTranslate_toLp_ae_eq (g : G) (f : G →C_c ℂ) :
    (regularTranslate ν g ((regularL2_memLp_compactlySupported ν f).toLp f) : G → ℂ)
      =ᵐ[ν] fun x ↦ f (g⁻¹ * x) := by
  exact ((regularL2_memLp_compactlySupported ν f).comp_measurePreserving
    (measurePreserving_mul_left ν g⁻¹)).coeFn_toLp

private theorem eq_regularTranslate_of_compactlySupported (g : G)
    (T : RegularL2 ν →L[ℂ] RegularL2 ν)
    (hT : ∀ f : G →C_c ℂ, (T ((regularL2_memLp_compactlySupported ν f).toLp f) : G → ℂ)
      =ᵐ[ν] fun x ↦ f (g⁻¹ * x)) (u : RegularL2 ν) : T u = regularTranslate ν g u := by
  refine (regularL2_compactlySupported_dense ν).induction_on u
    (isClosed_eq T.continuous (continuous_const_smul (DomMulAct.mk g⁻¹))) ?_
  intro f
  exact Lp.ext ((hT f).trans (regularTranslate_toLp_ae_eq ν g f).symm)

/-- Paper: Lemma 4.3.1.5(2), p. 176. Translation extends to a unique strongly
continuous linear action on Haar L². Its values on compactly supported
continuous functions agree almost everywhere with the original formula. -/
theorem existsUnique_regularL2_action :
    ∃! ρ : G →* (RegularL2 ν →L[ℂ] RegularL2 ν),
      (∀ f : RegularL2 ν, Continuous fun g ↦ ρ g f) ∧
      ∀ (g : G) (f : G →C_c ℂ),
        (ρ g ((regularL2_memLp_compactlySupported ν f).toLp f) : G → ℂ)
          =ᵐ[ν] fun x ↦ f (g⁻¹ * x) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let ρ : G →* (RegularL2 ν →L[ℂ] RegularL2 ν) :=
    { toFun := fun g ↦
        (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_mul_left ν g⁻¹)).toContinuousLinearMap
      map_one' := by
        ext f : 1
        change DomMulAct.mk (1 : G)⁻¹ • f = f
        simp
      map_mul' := by
        intro g h
        ext f : 1
        change DomMulAct.mk (g * h)⁻¹ • f = DomMulAct.mk g⁻¹ • DomMulAct.mk h⁻¹ • f
        rw [mul_inv_rev, DomMulAct.mk_mul]
        exact (inferInstance : MulAction Gᵈᵐᵃ (RegularL2 ν)).mul_smul _ _ _ }
  refine ⟨ρ, ⟨fun f ↦ ?_, regularTranslate_toLp_ae_eq ν⟩, ?_⟩
  · exact (DomMulAct.continuous_mk.comp continuous_inv).smul continuous_const
  · intro σ hσ
    ext g f : 2
    exact eq_regularTranslate_of_compactlySupported ν g (σ g) (hσ.2 g) f

/-- Paper: Lemma 4.3.1.5(2), p. 176. The regular representation uses the unique
strongly continuous extension of translation from compactly supported functions. -/
def regularL2Action : G →* (RegularL2 ν →L[ℂ] RegularL2 ν) :=
  Classical.choose (existsUnique_regularL2_action ν).exists

/-- Paper: Lemma 4.3.1.5(2), p. 176. The extended action agrees with
measure-preserving precomposition on every L² class. -/
theorem regularL2Action_apply (g : G) (f : RegularL2 ν) :
    regularL2Action ν g f = regularTranslate ν g f := by
  exact eq_regularTranslate_of_compactlySupported ν g _
    ((existsUnique_regularL2_action ν).exists.choose_spec.2 g) f

/-- Paper: Lemma 4.3.1.5(2), p. 176. Left translations preserve the Hermitian
inner product as in (4.3.1.5). The inverse translation formula follows separately from
the group action law for `regularL2Action`. -/
theorem regularL2Action_inner (g : G) (f h : RegularL2 ν) :
    ⟪regularL2Action ν g f, regularL2Action ν g h⟫_ℂ = ⟪f, h⟫_ℂ := by
  rw [regularL2Action_apply, regularL2Action_apply]
  exact (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_mul_left ν g⁻¹)).inner_map_map f h

/-- Paper: Lemma 4.3.1.5(3), p. 176. Composing the regular representation
with a continuous section of the module gives a strongly continuous
one-parameter group of unitary operators. -/
theorem regularL2Action_section (m : G →ₜ* ℝ≥0ˣ) (_hm : IsModulation m)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m) :
    (∀ f : RegularL2 ν, Continuous fun t ↦ ((regularL2Action ν).comp τ.toMonoidHom) t f) ∧
    ∀ (t : ℝ≥0ˣ) (f h : RegularL2 ν),
      ⟪regularL2Action ν (τ t) f, regularL2Action ν (τ t) h⟫_ℂ = ⟪f, h⟫_ℂ := by
  exact ⟨fun f ↦ ((existsUnique_regularL2_action ν).exists.choose_spec.1 f).comp τ.continuous,
    fun t ↦ regularL2Action_inner ν (τ t)⟩

end Regular

section Transform

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
  (ν : Measure G) [hν : ν.IsHaarMeasure]
  (ν₁ : Measure m.toMonoidHom.ker) [hν₁ : ν₁.IsHaarMeasure]

include hm hν hν₁

local notation "K" => m.toMonoidHom.ker

-- TODO(paper-gap): The Tamagawa measure reference after (4.3.2.1) is printed
-- as “Definition ??”. The statements use specified Haar measures instead.

omit [T2Space G] in
/-- Left translation by the kernel variable preserves square integrability on the product. -/
private theorem regularTranslate_memLp_prod (f : RegularL2 ν) :
    MemLp (fun p : K × G ↦ f ((p.1 : G)⁻¹ * p.2)) 2 (ν₁.prod ν) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have hshift : MeasurePreserving (fun p : K × G ↦ (p.1, (p.1 : G)⁻¹ * p.2))
      (ν₁.prod ν) (ν₁.prod ν) :=
    (MeasurePreserving.id ν₁).skew_product (g := fun k x ↦ (k : G)⁻¹ * x)
      (by unfold uncurry; fun_prop)
      (ae_of_all _ fun k ↦ (measurePreserving_mul_left ν (k : G)⁻¹).map_eq)
  exact ((Lp.memLp f).comp_snd ν₁).comp_measurePreserving hshift

/-- Paper: (4.3.2.1), p. 178. The character-weighted translate of an L²
representative is integrable on almost every norm-one fiber. -/
theorem regularIsotypic_ae_integrable (ω : PontryaginDual K) (f : RegularL2 ν) :
    ∀ᵐ x ∂ν, Integrable (fun k : K ↦ star (ω k : ℂ) * f ((k : G)⁻¹ * x)) ν₁ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have hsq := (regularTranslate_memLp_prod m hm ν ν₁ f).norm.integrable_sq
  filter_upwards [hsq.prod_left_ae] with x hx
  have hmeas : StronglyMeasurable (fun k : K ↦ f ((k : G)⁻¹ * x)) :=
    (Lp.stronglyMeasurable f).comp_measurable (by fun_prop)
  have h₂ := (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 hx
  exact (h₂.integrable (by norm_num)).bdd_mul (c := 1)
    (by fun_prop) (ae_of_all _ fun k ↦ by simp)

/-- The Hilbert-space integral of weighted translates agrees almost everywhere
with the scalar fiber integral. -/
private theorem regularIsotypic_integral_ae (ω : PontryaginDual K) (f : RegularL2 ν)
    (hint : Integrable (fun k : K ↦ star (ω k : ℂ) • regularTranslate ν (k : G) f) ν₁) :
    ((∫ k : K, star (ω k : ℂ) • regularTranslate ν (k : G) f ∂ν₁ : RegularL2 ν) : G → ℂ)
      =ᵐ[ν] fun x ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂ν₁ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  let U (k : K) (f : RegularL2 ν) := star (ω k : ℂ) • regularTranslate ν (k : G) f
  let F (k : K) (x : G) := star (ω k : ℂ) * f ((k : G)⁻¹ * x)
  -- On a set of finite measure the translated L² integrand is also in L¹.
  have hFin (s : Set G) (hμs : ν s < ∞) :
      Integrable (uncurry F) (ν₁.prod (ν.restrict s)) := by
    have : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.mpr hμs.ne
    have h₂ := (regularTranslate_memLp_prod m hm ν ν₁ f).mono_measure
      (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := s)))
    exact (h₂.integrable (by norm_num)).bdd_mul (c := 1)
      (show Continuous (fun p : K × G ↦ star (ω p.1 : ℂ)) by fun_prop).aestronglyMeasurable
      (ae_of_all _ fun p ↦ by simp)
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · exact fun s _ hs ↦ integrableOn_Lp_of_measure_ne_top (∫ k : K, U k f ∂ν₁) (by norm_num) hs.ne
  · exact fun s _ hs ↦ (hFin s hs).integral_prod_right
  · intro s hs hμs
    -- Pairing with the indicator of s computes the set integral of an L² class.
    let e := indicatorConstLp (μ := ν) 2 hs hμs.ne (1 : ℂ)
    have he (u : RegularL2 ν) : ⟪e, u⟫_ℂ = ∫ x in s, u x ∂ν := by
      simpa [e] using L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ hs hμs.ne (1 : ℂ) u
    rw [← he]
    change ⟪e, ∫ k : K, U k f ∂ν₁⟫_ℂ = ∫ x in s, ∫ k : K, F k x ∂ν₁ ∂ν
    rw [← integral_inner hint e, ← integral_integral_swap (hFin s hμs)]
    refine integral_congr_ae (ae_of_all _ fun k ↦ ?_)
    change ⟪e, U k f⟫_ℂ = ∫ x in s, F k x ∂ν
    rw [he]
    apply integral_congr_ae
    apply ae_restrict_of_ae
    filter_upwards [Lp.coeFn_smul (star (ω k : ℂ)) (regularTranslate ν (k : G) f),
      regularTranslate_ae_eq ν (k : G) f] with x h₁ h₂
    exact h₁.trans (congrArg (star (ω k : ℂ) * ·) h₂)

/-- Paper: (4.3.2.1), p. 178. Fiber averaging defines a continuous linear
operator on Haar L² with its stated almost-everywhere formula. -/
theorem existsUnique_regularIsotypicIntegral (ω : PontryaginDual K) :
    ∃! P : RegularL2 ν →L[ℂ] RegularL2 ν, ∀ f : RegularL2 ν,
      (P f : G → ℂ) =ᵐ[ν] fun x ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂ν₁ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let U (k : K) (f : RegularL2 ν) := star (ω k : ℂ) • regularTranslate ν (k : G) f
  have hi (f : RegularL2 ν) : Integrable (fun k ↦ U k f) ν₁ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (show Continuous (fun k : K ↦ star (ω k : ℂ)) by fun_prop).smul
      ((DomMulAct.continuous_mk.comp continuous_subtype_val.inv).smul continuous_const)
  let A : RegularL2 ν →ₗ[ℂ] RegularL2 ν :=
    { toFun := fun f ↦ ∫ k : K, U k f ∂ν₁
      map_add' := fun f g ↦ by
        simpa only [U, regularTranslate, smul_add] using integral_add (hi f) (hi g)
      map_smul' := fun c f ↦ by
        change (∫ k : K, U k (c • f) ∂ν₁) = c • ∫ k : K, U k f ∂ν₁
        rw [← integral_smul]
        apply integral_congr_ae
        exact ae_of_all _ fun k ↦ by
          simp only [U, regularTranslate, smul_comm (DomMulAct.mk _) c, smul_comm (star _) c] }
  let P := A.mkContinuous (ν₁.real univ) fun f ↦ by
    change ‖∫ k : K, U k f ∂ν₁‖ ≤ ν₁.real univ * ‖f‖
    rw [mul_comm]
    apply norm_integral_le_of_norm_le_const
    exact ae_of_all _ fun k ↦ by simp [U, regularTranslate, norm_smul]
  have hP (f : RegularL2 ν) :
      (P f : G → ℂ) =ᵐ[ν] fun x ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂ν₁ :=
    regularIsotypic_integral_ae m hm ν ν₁ ω f (hi f)
  refine ⟨P, hP, fun Q hQ ↦ ?_⟩
  ext f : 1
  exact Lp.ext ((hQ f).trans (hP f).symm)

/-- Paper: (4.3.2.1), p. 178. The unnormalized L² isotypic operator is
the continuous linear map given almost everywhere by integration over the kernel. -/
def regularIsotypicIntegral (ω : PontryaginDual K) : RegularL2 ν →L[ℂ] RegularL2 ν :=
  Classical.choose (existsUnique_regularIsotypicIntegral m hm ν ν₁ ω).exists

/-- The Bochner integral of the twisted orbit represents the isotypic average. -/
theorem regularIsotypicIntegral_eq_bochner (ω : PontryaginDual K) (f : RegularL2 ν)
    (hi : Integrable (fun k : K ↦ star (ω k : ℂ) • regularTranslate ν (k : G) f) ν₁) :
    regularIsotypicIntegral m hm ν ν₁ ω f =
      ∫ k : K, star (ω k : ℂ) • regularTranslate ν (k : G) f ∂ν₁ := by
  exact Lp.ext (((existsUnique_regularIsotypicIntegral m hm ν ν₁ ω).exists.choose_spec f).trans
    (regularIsotypic_integral_ae m hm ν ν₁ ω f hi).symm)

/-- Paper: (4.3.2.1), p. 178. The L² average agrees almost everywhere with
the integral using positive translation and the unconjugated character. -/
theorem regularIsotypicIntegral_ae_eq (ω : PontryaginDual K) (f : RegularL2 ν) :
    (regularIsotypicIntegral m hm ν ν₁ ω f : G → ℂ) =ᵐ[ν]
      fun x ↦ ∫ k : K, (ω k : ℂ) * f ((k : G) * x) ∂ν₁ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  refine ((existsUnique_regularIsotypicIntegral m hm ν ν₁ ω).exists.choose_spec f).trans ?_
  apply ae_of_all
  intro x
  symm
  simpa [← Circle.coe_inv_eq_conj] using (integral_inv_eq_self
    (fun k : K ↦ star (ω k : ℂ) * f ((k : G)⁻¹ * x)) ν₁)

variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

include hτ

omit hm hν hν₁ hτ in
/-- Paper: Text following (4.3.2.1), p. 178. The exponential pushforward of
Lebesgue measure is a multiplicative Haar measure on the positive reals. This justifies the
canonical Haar measure convention dt/t used there. -/
theorem positiveRealHaar_isHaarMeasure : positiveRealHaar.IsHaarMeasure := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let μ : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  have : μ.IsHaarMeasure := by
    have : IsFiniteMeasureOnCompacts μ :=
      inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    have : Measure.IsOpenPosMeasure μ :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    have : μ.IsMulLeftInvariant :=
      ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let h := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let e : Multiplicative ℝ ≃ₜ* ℝ≥0ˣ :=
    { h with
      map_mul' := fun x y ↦ by
        apply Units.ext
        apply NNReal.eq
        change Real.exp (x.toAdd + y.toAdd) = Real.exp x.toAdd * Real.exp y.toAdd
        exact Real.exp_add _ _ }
  have he (x : ℝ) :
      e (Multiplicative.ofAdd x) = Units.mk0 (Real.exp x).toNNReal (by positivity) := by
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  convert e.isHaarMeasure_map μ using 1
  unfold positiveRealHaar
  congr 1
  funext x
  exact (he x).symm

omit hν hν₁ [MeasurableSpace G] [BorelSpace G] in
/-- Use the section as a coordinate and invert the kernel variable to match the fiber integral. -/
private theorem exists_regularIsotypic_sectionEquiv :
    ∃ j : (K × ℝ≥0ˣ) ≃ₜ* G, ∀ p, j p = (p.1 : G)⁻¹ * τ p.2 := by
  let r : ℝ≥0ˣ ≃ₜ m.toMonoidHom.range :=
    { toFun := fun t ↦ ⟨t, τ t, hτ t⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  let h : (K × ℝ≥0ˣ) ≃ₜ* (K × m.toMonoidHom.range) :=
    { (Homeomorph.inv K).prodCongr r with
      map_mul' := fun a b ↦ Prod.ext (by simp [mul_comm]) rfl }
  let i : m.toMonoidHom.range →ₜ* ℝ≥0ˣ := ⟨m.toMonoidHom.range.subtype, continuous_subtype_val⟩
  let τr := τ.comp i
  obtain ⟨e, he⟩ := hm.exists_prod_equiv τr (fun t ↦ hτ t)
  exact ⟨h.trans e, fun p ↦ he p.1⁻¹ (r p.2)⟩

/-- Paper: (4.3.2.4), p. 178. Integration on the fibers parametrized by a
section is defined almost everywhere and gives an L² function for `dt/t`.
Deviation: We use fiber integration of a representative to define the
operator, since the restriction of an arbitrary L² class to the section
is undefined. -/
theorem regularIsotypicComponent_memLp (ω : PontryaginDual K) (f : RegularL2 ν) :
    (∀ᵐ t ∂positiveRealHaar,
      Integrable (fun k : K ↦ star (ω k : ℂ) * f ((k : G)⁻¹ * τ t)) ν₁) ∧
    MemLp (fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁)
      2 positiveRealHaar := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let logHomeo := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := logHomeo.isOpenEmbedding.locallyCompactSpace
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m hm τ hτ
  let η := ν₁.prod positiveRealHaar
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  -- Both Haar measures on G differ by a finite positive scalar.
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := by
    rw [Measure.isMulLeftInvariant_eq_smul (η.map j) ν]
    exact (Lp.memLp f).smul_measure_nnreal
  have hcomp := hmem.comp_of_map j.continuous.measurable.aemeasurable
  have hweighted : MemLp (fun p : K × ℝ≥0ˣ ↦ star (ω p.1 : ℂ) * f (j p)) 2 η := by
    apply hcomp.of_le
    · have hc : Continuous (fun p : K × ℝ≥0ˣ ↦ star (ω p.1 : ℂ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hcomp.aestronglyMeasurable
    · exact ae_of_all _ fun p ↦ by simp
  constructor
  · simpa only [hj] using
      (memLp_two_prod_left_ae hweighted).mono fun t ht ↦ ht.integrable (by norm_num)
  · simpa only [hj] using memLp_two_integral_prod_left hweighted

/-- Paper: (4.3.2.4), p. 178. The section gives the `dt/t` L² coordinate
of the unnormalized character average.
Deviation: The fiber integral is formed before passing to the L² class. -/
def regularIsotypicComponent (ω : PontryaginDual K) (f : RegularL2 ν) :
    RegularL2 positiveRealHaar :=
  (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω f).2.toLp
    (fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁)

/-- Almost-everywhere equality on the group pulls back to almost-everywhere equality
on almost every section fiber. -/
private theorem regularIsotypic_section_ae {u v : G → ℂ} (huv : u =ᵐ[ν] v) :
    ∀ᵐ t ∂positiveRealHaar, ∀ᵐ a : K ∂ν₁, u ((a : G)⁻¹ * τ t) = v ((a : G)⁻¹ * τ t) := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let logHomeo := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := logHomeo.isOpenEmbedding.locallyCompactSpace
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m hm τ hτ
  let η := ν₁.prod positiveRealHaar
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  have hmap : QuasiMeasurePreserving j η ν :=
    ⟨j.continuous.measurable.aemeasurable, Measure.absolutelyContinuous_isHaarMeasure _ _⟩
  have hp : ∀ᵐ t ∂positiveRealHaar, ∀ᵐ a : K ∂ν₁, u (j (a, t)) = v (j (a, t)) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      (hmap.ae_eq_comp huv))
  simpa only [hj] using hp

/-- Paper: (4.3.2.4), p. 178. Translation by a norm-one element acts on the
corresponding transformed coordinate by the character. -/
theorem regularIsotypicComponent_equivariant (ω : PontryaginDual K) (k : K) (f : RegularL2 ν) :
    regularIsotypicComponent m hm ν ν₁ τ hτ ω (regularTranslate ν (k : G) f) =
      (ω k : ℂ) • regularIsotypicComponent m hm ν ν₁ τ hτ ω f := by
  let f' := regularTranslate ν (k : G) f
  have hab := regularIsotypic_section_ae m hm ν ν₁ τ hτ (regularTranslate_ae_eq ν (k : G) f)
  let C := regularIsotypicComponent m hm ν ν₁ τ hτ ω
  have hC (v : RegularL2 ν) : (C v : ℝ≥0ˣ → ℂ) =ᵐ[positiveRealHaar] fun t ↦
      ∫ a : K, star (ω a : ℂ) * v ((a : G)⁻¹ * τ t) ∂ν₁ :=
    (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω v).2.coeFn_toLp
  apply Lp.ext
  filter_upwards [hC f', hC f, Lp.coeFn_smul (ω k : ℂ) (C f), hab] with t ht' ht hs htrans
  change (C f') t = ((ω k : ℂ) • C f) t
  rw [ht', hs]
  change _ = (ω k : ℂ) * (C f) t
  rw [ht, ← integral_const_mul, ← integral_mul_right_eq_self
    (μ := ν₁) (fun a : K ↦ (ω k : ℂ) * (star (ω a : ℂ) * f ((a : G)⁻¹ * τ t))) k]
  apply integral_congr_ae
  filter_upwards [htrans] with a ha
  rw [ha]
  simp only [map_mul, Subgroup.coe_mul, mul_inv_rev, Circle.coe_mul, star_mul', mul_assoc]
  rw [mul_left_comm (ω k : ℂ) (star (ω a : ℂ)), ← mul_assoc (ω k : ℂ)]
  simp [← Circle.coe_inv_eq_conj]

-- TODO(paper-gap): (4.3.2.3) evaluates ω on G before choosing its extension
-- from G¹. The section gives an extension trivial on its image.
-- TODO(paper-gap): (4.3.2.5) needs measure normalization. For G = ℝ>0,
-- ν = dt/t and ν₁ = 2 δ₁, the only component is multiplication by 2.

/-- One constant bounds all the finite sums of squared coordinate norms.
It records the total mass of the kernel and the change of Haar normalization. -/
private theorem exists_regularIsotypicComponent_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : RegularL2 ν) (s : Finset (PontryaginDual K)),
      ∑ ω ∈ s, ‖regularIsotypicComponent m hm ν ν₁ τ hτ ω f‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let logHomeo := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := logHomeo.isOpenEmbedding.locallyCompactSpace
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m hm τ hτ
  let η := ν₁.prod positiveRealHaar
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  let c := Measure.haarScalarFactor (η.map j) ν
  have hμ : η.map j = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨ν₁.real univ * (c : ℝ), mul_nonneg measureReal_nonneg c.coe_nonneg, fun f s ↦ ?_⟩
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := hμ ▸ (Lp.memLp f).smul_measure_nnreal
  have hcomp := hmem.comp_of_map j.continuous.measurable.aemeasurable
  have hb := sum_sq_character_integral_prod_le ν₁ hcomp
    (fun ω ↦ regularIsotypicComponent m hm ν ν₁ τ hτ ω f) (fun ω ↦ by
      simpa only [regularIsotypicComponent, Function.comp_apply, hj] using (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω f).2.coeFn_toLp) s
  have hn : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp f)
  have heq : ∫ x, ‖f x‖ ^ 2 ∂η.map j = ∫ p, ‖f (j p)‖ ^ 2 ∂η :=
    integral_map j.continuous.measurable.aemeasurable (hmem.aestronglyMeasurable.norm.pow 2)
  calc
    _ ≤ ν₁.real univ * ∫ p, ‖f (j p)‖ ^ 2 ∂η := hb
    _ = _ := by
      rw [← heq, hμ, integral_smul_nnreal_measure, hn, mul_assoc]
      rfl

/-- Paper: (4.3.2.7), p. 178. The family of all coordinates belongs to the
Hilbert direct sum. -/
theorem regularIsotypicTransform_memℓp (f : RegularL2 ν) :
    Memℓp (fun ω : PontryaginDual K ↦ regularIsotypicComponent m hm ν ν₁ τ hτ ω f) 2 := by
  obtain ⟨C, _, hC⟩ := exists_regularIsotypicComponent_bound m hm ν ν₁ τ hτ
  apply memℓp_gen' (C := C * ‖f‖ ^ 2)
  intro s
  simpa using hC f s

/-- Paper: (4.3.2.7), p. 178. The transform takes all the character
coordinates together in the Hilbert direct sum. -/
def regularIsotypicTransform (f : RegularL2 ν) :
    lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2 :=
  ⟨fun ω ↦ regularIsotypicComponent m hm ν ν₁ τ hτ ω f,
    regularIsotypicTransform_memℓp m hm ν ν₁ τ hτ f⟩

/-- Paper: (4.3.2.7), p. 178. The coordinate indexed by a character is the
almost-everywhere integral with that character's conjugate. -/
theorem regularIsotypicTransform_ae_eq (ω : PontryaginDual K) (f : RegularL2 ν) :
    (regularIsotypicTransform m hm ν ν₁ τ hτ f ω : ℝ≥0ˣ → ℂ) =ᵐ[positiveRealHaar]
      fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁ := by
  exact (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω f).2.coeFn_toLp

/-- Paper: (4.3.2.7), p. 178. The transform is linear and continuous
for the Hilbert direct sum topology. -/
theorem regularIsotypicTransform_continuousLinear :
    ∃ T : RegularL2 ν →L[ℂ] lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2,
      ∀ f : RegularL2 ν, T f = regularIsotypicTransform m hm ν ν₁ τ hτ f := by
  let T := regularIsotypicTransform m hm ν ν₁ τ hτ
  let C := regularIsotypicComponent m hm ν ν₁ τ hτ
  have hC (ω : PontryaginDual K) (f : RegularL2 ν) : (C ω f : ℝ≥0ˣ → ℂ) =ᵐ[positiveRealHaar]
      fun t ↦ ∫ a : K, star (ω a : ℂ) * f ((a : G)⁻¹ * τ t) ∂ν₁ :=
    (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω f).2.coeFn_toLp
  let L : RegularL2 ν →ₗ[ℂ] lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2 :=
    { toFun := T
      map_add' := by
        intro f g
        apply lp.ext
        funext ω
        change C ω (f + g) = C ω f + C ω g
        apply Lp.ext
        have ha := regularIsotypic_section_ae m hm ν ν₁ τ hτ (Lp.coeFn_add f g)
        filter_upwards [hC ω (f + g), hC ω f, hC ω g, Lp.coeFn_add (C ω f) (C ω g),
          (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω f).1,
          (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω g).1, ha]
          with t hfg hf hg hs hi hj ht
        rw [hfg, hs, Pi.add_apply, hf, hg, ← integral_add hi hj]
        apply integral_congr_ae
        filter_upwards [ht] with a ha
        simp only [ha, Pi.add_apply, mul_add]
      map_smul' := by
        intro z f
        apply lp.ext
        funext ω
        change C ω (z • f) = z • C ω f
        apply Lp.ext
        have ha := regularIsotypic_section_ae m hm ν ν₁ τ hτ (Lp.coeFn_smul z f)
        filter_upwards [hC ω (z • f), hC ω f, Lp.coeFn_smul z (C ω f), ha]
          with t hzf hf hs ht
        rw [hzf, hs, Pi.smul_apply, smul_eq_mul, hf, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ht] with a ha
        simp only [ha, Pi.smul_apply, smul_eq_mul, mul_left_comm z] }
  obtain ⟨B, hB, hbound⟩ := exists_regularIsotypicComponent_bound m hm ν ν₁ τ hτ
  refine ⟨L.mkContinuous (Real.sqrt B) (fun f ↦ ?_), fun _ ↦ rfl⟩
  apply lp.norm_le_of_forall_sum_le (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  intro s
  simpa [L, T, regularIsotypicTransform, mul_pow, Real.sq_sqrt hB] using hbound f s

/-- Lift each prescribed coefficient along the section and multiply by its character.
The lifts are orthogonal, have a common squared-norm scale, and have the expected
character integrals. -/
private theorem exists_regularIsotypic_synthesisFamily
    (y : lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2) :
    ∃ (B : ℝ) (v : PontryaginDual K → RegularL2 ν),
      (∀ ω, ‖v ω‖ ^ 2 = B * ‖y ω‖ ^ 2) ∧
      (Pairwise fun χ ψ ↦ ⟪v χ, v ψ⟫_ℂ = 0) ∧
      ∀ χ ω, regularIsotypicComponent m hm ν ν₁ τ hτ χ (v ω) =
        (∫ a, star (χ a : ℂ) * (ω a : ℂ) ∂ν₁) • y ω := by
  classical
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let logHomeo := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := logHomeo.isOpenEmbedding.locallyCompactSpace
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m hm τ hτ
  have : SecondCountableTopology (K × ℝ≥0ˣ) := j.toHomeomorph.isEmbedding.secondCountableTopology
  let η := ν₁.prod positiveRealHaar
  have : (ν.map j.symm).IsHaarMeasure := j.symm.isHaarMeasure_map ν
  let c := Measure.haarScalarFactor (ν.map j.symm) η
  have hμ : ν.map j.symm = c • η := Measure.isMulLeftInvariant_eq_smul _ _
  have hint {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : K × ℝ≥0ˣ → E) :
      ∫ x, F (j.symm x) ∂ν = c • ∫ p, F p ∂η := by
    have he := integral_map_equiv (μ := ν) j.symm.toHomeomorph.toMeasurableEquiv F
    change ∫ p, F p ∂ν.map j.symm = ∫ x, F (j.symm x) ∂ν at he
    rw [← he, hμ, integral_smul_nnreal_measure]
  let A (ω : PontryaginDual K) (p : K × ℝ≥0ˣ) : ℂ := (ω p.1 : ℂ) * y ω p.2
  have hA (ω : PontryaginDual K) : MemLp (A ω) 2 η := by
    have hy := (Lp.memLp (y ω)).comp_snd ν₁
    apply hy.of_le
    · have hc : Continuous (fun p : K × ℝ≥0ˣ ↦ (ω p.1 : ℂ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hy.aestronglyMeasurable
    · exact ae_of_all _ fun p ↦ by simp [A]
  have hv (ω : PontryaginDual K) : MemLp (A ω ∘ j.symm) 2 ν :=
    (show MemLp (A ω) 2 (ν.map j.symm) from hμ ▸ (hA ω).smul_measure_nnreal).comp_of_map
      j.symm.continuous.measurable.aemeasurable
  let v (ω : PontryaginDual K) := (hv ω).toLp (A ω ∘ j.symm)
  refine ⟨(c : ℝ) * ν₁.real univ, v, fun ω ↦ ?_, fun χ ψ hχψ ↦ ?_, fun χ ω ↦ ?_⟩
  · have hy : ‖y ω‖ ^ 2 = ∫ t, ‖y ω t‖ ^ 2 ∂positiveRealHaar := by
      simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp (y ω))
    rw [norm_sq_toLp_two (hv ω), hy]
    have he := hint (fun p ↦ ‖A ω p‖ ^ 2)
    change ∫ x, ‖A ω (j.symm x)‖ ^ 2 ∂ν = _ at he ⊢
    rw [he]
    have he' := integral_fun_snd (μ := ν₁) (ν := positiveRealHaar) (fun t ↦ ‖y ω t‖ ^ 2)
    simp only [A, norm_mul, Circle.norm_coe, one_mul]
    rw [he', mul_assoc]
    rfl
  · change ⟪v χ, v ψ⟫_ℂ = 0
    rw [L2.inner_def]
    let F (p : K × ℝ≥0ˣ) := (star (χ p.1 : ℂ) * (ψ p.1 : ℂ)) *
      (star (y χ p.2) * y ψ p.2)
    calc
      _ = ∫ x, F (j.symm x) ∂ν := by
        apply integral_congr_ae
        filter_upwards [(hv χ).coeFn_toLp, (hv ψ).coeFn_toLp] with x hx hy
        change ⟪v χ x, v ψ x⟫_ℂ = _
        rw [show v χ x = _ from hx, show v ψ x = _ from hy]
        simp only [RCLike.inner_apply, Function.comp_apply, F, A, starRingEnd_apply, star_mul']
        ring
      _ = 0 := by
        rw [hint, show (∫ p, F p ∂η) = _ from integral_prod_mul
          (fun a ↦ star (χ a : ℂ) * (ψ a : ℂ)) (fun t ↦ star (y χ t) * y ψ t)]
        rw [integral_character_pair ν₁ χ ψ]
        simp [hχψ]
  · let d := ∫ a, star (χ a : ℂ) * (ω a : ℂ) ∂ν₁
    apply Lp.ext
    have hC := (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ χ (v ω)).2.coeFn_toLp
    have ha := regularIsotypic_section_ae m hm ν ν₁ τ hτ (hv ω).coeFn_toLp
    filter_upwards [hC, Lp.coeFn_smul d (y ω), ha] with t ht hs hrep
    change regularIsotypicComponent m hm ν ν₁ τ hτ χ (v ω) t = (d • y ω) t
    rw [show regularIsotypicComponent m hm ν ν₁ τ hτ χ (v ω) t = _ from ht, hs]
    change _ = d * y ω t
    rw [show d * y ω t = _ from (integral_mul_const (y ω t) _).symm]
    apply integral_congr_ae
    filter_upwards [hrep] with a ha
    rw [show v ω ((a : G)⁻¹ * τ t) = _ from ha]
    simp only [Function.comp_apply, ← hj (a, t), j.symm_apply_apply, A, mul_assoc]

/-- Paper: Lemma 4.3.2.2, p. 179. Every square-summable family of L²
coordinates is in the range of the transform. -/
theorem regularIsotypicTransform_surjective :
    Surjective (regularIsotypicTransform m hm ν ν₁ τ hτ) := by
  classical
  intro y
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm ν ν₁ τ hτ
  obtain ⟨B, v, hn, ho, hcoord⟩ := exists_regularIsotypic_synthesisFamily m hm ν ν₁ τ hτ y
  have hy : Summable (fun ω ↦ ‖y ω‖ ^ 2) := by
    simpa using (lp.memℓp y).summable (by norm_num)
  have hs : Summable v := (summable_iff_summable_sq_norm_of_orthogonal ho).2
    (by simpa only [hn] using hy.mul_left B)
  let d : ℂ := ν₁.real univ
  have hd : d ≠ 0 := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp
      (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
    dsimp [d]
    exact_mod_cast (measureReal_univ_pos (μ := ν₁)).ne'
  have hsingle (ω : PontryaginDual K) : T (v ω) = d • lp.single 2 ω (y ω) := by
    apply lp.ext
    funext χ
    rw [hT]
    change regularIsotypicComponent m hm ν ν₁ τ hτ χ (v ω) = _
    rw [hcoord, integral_character_pair, lp.coeFn_smul, Pi.smul_apply]
    by_cases h : χ = ω
    · subst χ
      simp [d]
    · simp [h]
  have hsum : HasSum (fun ω ↦ d • lp.single 2 ω (y ω)) (T (∑' ω, v ω)) :=
    (hs.hasSum.map T T.continuous).congr_fun fun ω ↦ (hsingle ω).symm
  have he := hsum.unique ((lp.hasSum_single (by simp) y).const_smul d)
  refine ⟨d⁻¹ • ∑' ω, v ω, ?_⟩
  rw [← hT, map_smul, he, smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- Paper: Lemma 4.3.2.2, p. 179. The Hilbert sum of the isotypic coordinates
determines the original L² class.
Deviation: Injectivity holds for arbitrary Haar normalizations. -/
theorem regularIsotypicTransform_injective :
    Injective (regularIsotypicTransform m hm ν ν₁ τ hτ) := by
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm ν ν₁ τ hτ
  rw [← funext hT]
  apply (LinearMap.ker_eq_bot.mp _ : Injective T.toLinearMap)
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hf0 : regularIsotypicTransform m hm ν ν₁ τ hτ f = 0 := (hT f).symm.trans hf
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : LocallyCompactSpace K := hm.isCompact_ker.isClosed.locallyCompactSpace
  have : SecondCountableTopology K := Subtype.secondCountableTopology (K : Set G)
  have : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  have : SecondCountableTopology (PontryaginDual K) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  have : Countable (PontryaginDual K) := countable_of_Lindelof_of_discrete
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let logHomeo := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := logHomeo.isOpenEmbedding.locallyCompactSpace
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m hm τ hτ
  let η := ν₁.prod positiveRealHaar
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := by
    rw [Measure.isMulLeftInvariant_eq_smul (η.map j) ν]
    exact (Lp.memLp f).smul_measure_nnreal
  have hjm := j.continuous.measurable
  have hcoeff (χ : PontryaginDual K) :
      (fun t ↦ ∫ k : K, star (χ k : ℂ) * f (j (k, t)) ∂ν₁) =ᵐ[positiveRealHaar] 0 := by
    have h := regularIsotypicTransform_ae_eq m hm ν ν₁ τ hτ χ f
    rw [hf0, lp.coeFn_zero, Pi.zero_apply] at h
    simpa only [hj] using h.symm.trans (Lp.coeFn_zero ℂ 2 positiveRealHaar)
  -- A common full-measure set of fibers works for all characters.
  have hfiber : ∀ᵐ t ∂positiveRealHaar, ∀ᵐ k ∂ν₁, f (j (k, t)) = 0 := by
    filter_upwards [memLp_two_prod_left_ae (hmem.comp_of_map hjm.aemeasurable),
      ae_all_iff.mpr hcoeff] with t ht hc
    exact ae_eq_zero_of_character_integral_eq_zero ν₁ ht hc
  have hmeas : MeasurableSet {x : G | f x = 0} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable f).measurable measurable_const
  have hprod : ∀ᵐ p ∂η, f (j p) = 0 :=
    (Measure.ae_prod_iff_ae_ae (hjm hmeas)).2
      ((Measure.ae_ae_comm (hjm hmeas)).2 hfiber)
  have hzero : ∀ᵐ x ∂η.map j, f x = 0 := (ae_map_iff hjm.aemeasurable hmeas).2 hprod
  have hae : (f : G → ℂ) =ᵐ[ν] 0 :=
    (Measure.absolutelyContinuous_isHaarMeasure ν (η.map j)).ae_le hzero
  exact Lp.ext (hae.trans (Lp.coeFn_zero ℂ 2 ν).symm)

/-- Paper: Lemma 4.3.2.2, p. 179. The squared norm of the isotypic transform
scales by the mass of the norm-one subgroup times the product Haar measure ratio.
Deviation: The scaling factor accounts for the arbitrary Haar normalizations (ERRATA I73). -/
theorem regularIsotypicTransform_norm_sq (c : ℝ≥0∞)
    (hc : (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = c • ν)
    (f : RegularL2 ν) :
    ‖regularIsotypicTransform m hm ν ν₁ τ hτ f‖ ^ 2 = ν₁.real univ * c.toReal * ‖f‖ ^ 2 := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : SecondCountableTopology K := Subtype.secondCountableTopology (K : Set G)
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let logHomeo := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := logHomeo.isOpenEmbedding.locallyCompactSpace
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m hm τ hτ
  let η := ν₁.prod positiveRealHaar
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := by
    rw [Measure.isMulLeftInvariant_eq_smul (η.map j) ν]
    exact (Lp.memLp f).smul_measure_nnreal
  have hcomp := hmem.comp_of_map j.continuous.measurable.aemeasurable
  have hmap : η.map j = c • ν := by
    let q (z : K × ℝ≥0ˣ) : G := (z.1 : G) * τ z.2
    have hq : Measurable q :=
      (continuous_subtype_val.comp continuous_fst).measurable.mul
        (τ.continuous.measurable.comp measurable_snd)
    have hinv : MeasurePreserving (Prod.map (Inv.inv : K → K) id) η η :=
      (Measure.measurePreserving_inv ν₁).prod (MeasurePreserving.id positiveRealHaar)
    rw [show (j : K × ℝ≥0ˣ → G) = q ∘ Prod.map Inv.inv id from funext hj,
      ← Measure.map_map hq hinv.measurable, hinv.map_eq]
    exact hc
  let y := regularIsotypicTransform m hm ν ν₁ τ hτ f
  have hy : HasSum (fun χ ↦ ‖y χ‖ ^ 2) (‖y‖ ^ 2) := by
    simpa using lp.hasSum_norm (by norm_num) y
  have hn : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp f)
  calc
    ‖y‖ ^ 2 = ∑' χ, ‖y χ‖ ^ 2 := hy.tsum_eq.symm
    _ = ν₁.real univ * ∫ p, ‖f (j p)‖ ^ 2 ∂η := by
      refine tsum_sq_character_integral_prod ν₁ hcomp y (fun χ ↦ ?_)
      simpa only [Function.comp_apply, hj] using
        regularIsotypicTransform_ae_eq m hm ν ν₁ τ hτ χ f
    _ = _ := by
      have heq : ∫ x, ‖f x‖ ^ 2 ∂η.map j = ∫ p, ‖f (j p)‖ ^ 2 ∂η :=
        integral_map j.continuous.measurable.aemeasurable (hmem.aestronglyMeasurable.norm.pow 2)
      rw [← heq, hmap, integral_smul_measure, hn, mul_assoc]
      rfl

-- TODO(paper-gap): Lemma 4.3.2.2's isometry and the isometry asserted on
-- p. 180 fail for the same measure rescaling as (4.3.2.5).

end Transform

end RiemannMasullo
