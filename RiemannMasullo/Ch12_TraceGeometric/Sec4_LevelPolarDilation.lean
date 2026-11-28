module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# At twist below one, the polar-free level loses the integral condition

The proof of Theorem 12.5.1.1 (p. 520) uses Theorem 12.4.1.1 with two polar Mellin values
subtracted, `M(φ)(|·|^(1/2))` and `M(φ)(|·|^(-1/2))`. `Sec4_LevelPolarComplement` shows that the
trace on the polar-free level differs from the trace on the full band by the diagonal entries on
the complement of the level, which has dimension at most two, one direction for each moment of a
test: its value at zero and its integral. This file shows that at a twist `0 < a < 1`, and so at
the twist `1/2` of §12.5, the integral condition does not survive the closure that defines the
level, for every number field and every finite set of places.

* `sAdeleSchwartzFourier_unitTranslate_zero`. Translating a test by an S-idele `u` multiplies the
  value of its Fourier transform at zero, its integral, by `|u|`. The change of variables is
  `levelDilation_integral_unit_mul`, from the private chain of `Sec4` repeated here.
* `norm_sq_sLocalFullPWThetaSobolevMap_unitTranslate_le`. The full theta class of the translate has
  squared weighted norm at most `|u| ^ (2a) (2 (1 + log² |u|)) ^ (s/2)` times that of the test,
  by the translation invariance of the quotient Haar measure.
* `sLocalFullPWThetaSobolevMap_mem_level_of_eval_zero`. So the dilates `|u|⁻¹ · (translate by u)`
  of a test keep its integral, divide its value at zero by `|u|`, and have theta classes of norm
  at most `|u| ^ (a - 1)` times a power of `log |u|`, which tends to zero for `a < 1`. Subtracting
  them corrects the integral of a test that vanishes at zero, so the full theta class of every
  test of the product region that vanishes at zero lies in the level.
* `sLocalPWSobolev_polarComplement_le_one`. Hence the complement of the level in the full band has
  dimension at most one, and each of its vectors represents a multiple of the value at zero alone.

So the polar term of `sLocalLevel_trace_asymptotic_of_full_comparison` is a single diagonal
entry. The level removes at most one of the two polar directions that p. 520 subtracts.

Not shown here: that the value at zero is a continuous functional on the full band, so that the
complement has dimension exactly one, and the value of the remaining diagonal entry.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology InnerProductSpace

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

section Modulus

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S

/-- For an additive integrand vanishing off the units, its multiplicative integral weighted by
the idelic norm is its additive integral times the finite-place measure factor. A copy of a
private lemma of `Sec4`. -/
theorem levelDilation_integral_units (a : Aₛ → ℂ)
    (ha : ∀ t, t ∉ range (Units.val : Iₛ → Aₛ) → a t = 0) :
    (∫ t : Iₛ, (normS(t) : ℂ) * a t.val ∂μₛ) =
      (sLocalTraceMeasureFactor S : ℂ) * ∫ t, a t ∂νₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  let n (t : Aₛ) := modS(t)
  have hn (t : Iₛ) : normS(t) = n t.val := by simp [n, sIdeleNorm, Units.coe_prod]
  have hm : Continuous n := by
    unfold n
    exact (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let c := sLocalTraceMeasureFactor (F := F) S
  have hc : 0 ≤ c := by
    apply Finset.prod_nonneg
    intro v _
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hv.le)
  let d (t : Aₛ) := ENNReal.ofReal (c / n t)
  have hd : Measurable d := (measurable_const.div hm.measurable).ennreal_ofReal
  simp_rw [hn]
  rw [← ho.measurableEmbedding.integral_map (μ := μₛ) (fun t ↦ (n t : ℂ) * a t),
    sLocalTrace_measure_density]
  change (∫ t, (n t : ℂ) * a t ∂((νₛ).restrict _).withDensity d) = _
  rw [integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero ha, ← integral_const_mul]
  apply integral_congr_ae
  apply (ae_restrict_iff' ho.isOpen_range.measurableSet).2
  apply ae_of_all
  rintro _ ⟨t, rfl⟩
  have hpos : 0 < n t.val := (hn t) ▸ NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S t))
  simp only [d, ENNReal.toReal_ofReal (div_nonneg hc hpos.le), Complex.real_smul,
    Complex.ofReal_div]
  change (c : ℂ) / _ * (_ * _) = (c : ℂ) * _
  field_simp [Complex.ofReal_ne_zero.mpr hpos.ne']

theorem levelDilation_neBot_of_norm_lt_one {K : Type*} [NormedField K] (a : K)
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) : (𝓝[≠] (0 : K)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_of_tendsto
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha) (Eventually.of_forall fun n ↦ pow_ne_zero n ha0))

theorem levelDilation_finite_neBot (v : HeightOneSpectrum (𝓞 F)) :
    (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact levelDilation_neBot_of_norm_lt_one (π : v.adicCompletion F) hπ.ne_zero
    (Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one)

theorem levelDilation_infinite_neBot (w : InfinitePlace F) :
    (𝓝[≠] (0 : w.Completion)).NeBot := by
  let a : w.Completion := ((WithAbs.equiv w.1).symm (2⁻¹ : F) : WithAbs w.1)
  have h2 : w (2 : F) = 2 := by simpa using w.map_natCast 2
  have hval : ‖a‖ = 2⁻¹ := by
    rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply, map_inv₀, h2]
  refine levelDilation_neBot_of_norm_lt_one a (fun h ↦ ?_) (by rw [hval]; norm_num)
  rw [h, norm_zero] at hval
  norm_num at hval

/-- The S-adeles with a zero coordinate form a null set for additive Tamagawa measure. A copy of
a private lemma of `Sec4`. -/
theorem levelDilation_nonunits_null :
    νₛ (range (Units.val : Iₛ → Aₛ))ᶜ = 0 := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let (w : InfinitePlace F) : (𝓝[≠] (0 : w.Completion)).NeBot := levelDilation_infinite_neBot w
  let (v : S) : (𝓝[≠] (0 : v.val.adicCompletion F)).NeBot := levelDilation_finite_neBot v.val
  have hw (w : InfinitePlace F) : infiniteLocalAdditiveTamagawaMeasure F w {0} = 0 :=
    measure_singleton 0
  have hv (v : S) : finiteLocalAdditiveTamagawaMeasure F v.val {0} = 0 :=
    measure_singleton 0
  have hsub : (range (Units.val : Iₛ → Aₛ))ᶜ ⊆
      (⋃ w : InfinitePlace F, Prod.fst ⁻¹' (Function.eval w ⁻¹' {0})) ∪
        ⋃ v : S, Prod.snd ⁻¹' (Function.eval v ⁻¹' {0}) := by
    intro a ha
    by_contra h
    simp only [mem_union, mem_iUnion, not_or, not_exists, mem_preimage, Function.eval,
      mem_singleton_iff] at h
    have hu : IsUnit a := Prod.isUnit_iff.mpr
      ⟨Pi.isUnit_iff.mpr fun w ↦ isUnit_iff_ne_zero.mpr (h.1 w),
        Pi.isUnit_iff.mpr fun v ↦ isUnit_iff_ne_zero.mpr (h.2 v)⟩
    exact ha ⟨hu.unit, rfl⟩
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun w ↦ ?_)
    (measure_iUnion_null fun v ↦ ?_))
  · rw [← prod_univ]
    change ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))) (_ ×ˢ _) = 0
    rw [Measure.prod_prod, Measure.pi_eval_preimage_null _ (hw w), zero_mul]
  · rw [← univ_prod]
    change ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))) (_ ×ˢ _) = 0
    rw [Measure.prod_prod, Measure.pi_eval_preimage_null
      (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) (i := v) (hv v), mul_zero]

/-- Paper: (12.4.1.22)–(12.4.1.23), p. 518. The change of variable `w = x u` by an S-idele
scales additive Tamagawa measure by the S-idelic norm: `∫ g(x u) du = |x|⁻¹ ∫ g`. This is
`Sec4`'s private band version with the band removed. -/
theorem levelDilation_integral_unit_mul (g : Aₛ → ℂ) (x : Iₛ) :
    ∫ u, g (x.val * u) ∂νₛ = ((normS(x))⁻¹ : ℂ) * ∫ w, g w ∂νₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  have hfull : ∀ᵐ u ∂νₛ, u ∈ range (Units.val : Iₛ → Aₛ) :=
    measure_eq_zero_iff_ae_notMem.mp levelDilation_nonunits_null |>.mono fun _ h ↦ not_not.mp h
  let c := sLocalTraceMeasureFactor (F := F) S
  have hc : (c : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ ↦ ?_)
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_ne_zero (by linarith) (sub_pos.mpr hv).ne'
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  have key (k : Aₛ → ℂ) :
      (∫ t : Iₛ, (normS(t) : ℂ) * (range (Units.val : Iₛ → Aₛ)).indicator k t.val ∂μₛ) =
        (c : ℂ) * ∫ u, k u ∂νₛ := by
    rw [levelDilation_integral_units _ (fun t ht ↦ indicator_of_notMem ht _),
      integral_indicator ho.isOpen_range.measurableSet,
      Measure.restrict_eq_self_of_ae_mem hfull]
  have hpt (t : Iₛ) : (normS(x⁻¹ * t) : ℂ) * (range (Units.val : Iₛ → Aₛ)).indicator
        (fun u ↦ g (x.val * u)) (x⁻¹ * t).val =
      ((normS(x))⁻¹ : ℂ) * ((normS(t) : ℂ) * (range (Units.val : Iₛ → Aₛ)).indicator g t.val) := by
    rw [indicator_of_mem (mem_range_self (x⁻¹ * t)), indicator_of_mem (mem_range_self t)]
    have hn : normS(x⁻¹ * t) = (normS(x))⁻¹ * normS(t) := by simp [map_mul, map_inv]
    rw [hn]
    simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    push_cast
    ring
  have h1 := key (fun u ↦ g (x.val * u))
  rw [← integral_mul_left_eq_self _ x⁻¹] at h1
  simp only [hpt, integral_const_mul] at h1
  rw [key] at h1
  apply mul_left_cancel₀ hc
  rw [← h1]
  ring

/-- Paper: §3.3.1, p. 128, with (12.4.1.22)–(12.4.1.23), p. 518. The Fourier transform at zero of
the translate of a test by an S-idele `u` is `|u|` times the Fourier transform of the test at
zero. -/
theorem sAdeleSchwartzFourier_unitTranslate_zero (u : Iₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd 0) =
      (normS(u) : ℂ) * sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) := by
  rw [sAdeleSchwartzFourier_apply_zero, sAdeleSchwartzFourier_apply_zero]
  have h := levelDilation_integral_unit_mul (fun w ↦ f (Multiplicative.ofAdd w)) u⁻¹
  have hn : normS(u⁻¹) = (normS(u))⁻¹ := by simp [map_inv]
  simp only [hn] at h
  have hpos : (normS(u) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S u))).ne'
  push_cast at h
  rw [inv_inv] at h
  exact h

/-- A continuous section of the S-idelic norm, through one infinite place. A copy of a private
lemma of `Sec4`. -/
theorem levelDilation_exists_normSection :
    ∃ τ : ℝ≥0ˣ →ₜ* Iₛ, RightInverse τ (sIdeleNorm F S) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  refine ⟨⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩, fun t ↦ ?_⟩
  let A := integralAdelesOutside F S
  have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
    simp only [A, integralAdelesOutside, Subring.mem_iInf]
    intro v _
    exact (v.adicCompletionIntegers F).one_mem
  have ht : s t ∈ A.toSubmonoid.units :=
    ⟨hmem t, by
      change ((s t)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem t⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm.trans (singlePlaceIdeleNormSection_rightInverse F w t)

end Modulus

section AbstractOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A linear map that vanishes on the kernel of a linear functional factors through it. -/
theorem exists_comp_eq_of_ker_le_scalar {X W : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup W] [Module ℂ W] (q : X →ₗ[ℂ] ℂ) (π : X →ₗ[ℂ] W)
    (h : LinearMap.ker q ≤ LinearMap.ker π) : ∃ g : ℂ →ₗ[ℂ] W, g ∘ₗ q = π := by
  let π' := (LinearMap.ker q).liftQ π h
  let g₀ : LinearMap.range q →ₗ[ℂ] W := π' ∘ₗ q.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g₀
  refine ⟨g, LinearMap.ext fun x ↦ ?_⟩
  have h1 : g (q x) = g₀ ⟨q x, LinearMap.mem_range_self q x⟩ := by
    rw [← hg]
    rfl
  rw [LinearMap.comp_apply, h1]
  simp only [g₀, π', LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- Reconstruction: let `B` be the closure of the image under `Θ` of a space `Y` of tests, and
`V ≤ B` a closed subspace that contains the image of every test of `Y` in the kernel of one
linear functional `ℓ`. Then the complement of `V` in `B` has dimension at most one, and each of
its vectors represents a multiple of `ℓ` on `Y`. -/
theorem finrank_inf_orthogonal_le_one {X : Type*} [AddCommGroup X] [Module ℂ X]
    (Θ : X →ₗ[ℂ] H) (Y : Submodule ℂ X) (ℓ : X →ₗ[ℂ] ℂ) (B V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (hB : B = (Y.map Θ).topologicalClosure)
    (hV : ∀ f ∈ Y, ℓ f = 0 → Θ f ∈ V) (hVB : V ≤ B) :
    FiniteDimensional ℂ ↥(B ⊓ Vᗮ) ∧ Module.finrank ℂ ↥(B ⊓ Vᗮ) ≤ 1 ∧
      ∀ e ∈ B ⊓ Vᗮ, ∃ c : ℂ, ∀ f ∈ Y, ⟪e, Θ f⟫_ℂ = c * ℓ f := by
  subst hB
  set B := (Y.map Θ).topologicalClosure
  have hmemB : ∀ f ∈ Y, Θ f ∈ B := fun f hf ↦
    Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hf)
  let P : H →L[ℂ] H := Vᗮ.starProjection
  let q : Y →ₗ[ℂ] ℂ := ℓ ∘ₗ Y.subtype
  let π : Y →ₗ[ℂ] H := P.toLinearMap ∘ₗ Θ ∘ₗ Y.subtype
  have hker : LinearMap.ker q ≤ LinearMap.ker π := by
    intro y hy
    simp only [LinearMap.mem_ker, q, π, LinearMap.comp_apply, Submodule.coe_subtype] at hy ⊢
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (Submodule.le_orthogonal_orthogonal V (hV y y.2 hy))
  obtain ⟨g, hg⟩ := exists_comp_eq_of_ker_le_scalar q π hker
  have hπg : LinearMap.range π ≤ LinearMap.range g := by
    rw [← hg, LinearMap.range_comp]
    exact LinearMap.map_le_range
  have hfin : FiniteDimensional ℂ (LinearMap.range π) :=
    Submodule.finiteDimensional_of_le hπg
  have hrange : B ⊓ Vᗮ = LinearMap.range π := by
    apply le_antisymm
    · intro e he
      have hcl : IsClosed (LinearMap.range π : Set H) := Submodule.isClosed_of_finiteDimensional _
      have hBle : B ≤ (LinearMap.range π).comap P.toLinearMap := by
        refine Submodule.topologicalClosure_minimal _ ?_ (hcl.preimage P.continuous)
        rintro _ ⟨f, hf, rfl⟩
        exact ⟨⟨f, hf⟩, rfl⟩
      have h1 := hBle he.1
      rwa [Submodule.mem_comap, ContinuousLinearMap.coe_coe,
        show P e = e from Submodule.starProjection_eq_self_iff.mpr he.2] at h1
    · rintro _ ⟨y, rfl⟩
      refine ⟨?_, Submodule.starProjection_apply_mem _ _⟩
      change Vᗮ.starProjection (Θ y) ∈ B
      rw [Submodule.starProjection_orthogonal_val]
      exact B.sub_mem (hmemB y y.2) (hVB (Submodule.starProjection_apply_mem V _))
  refine ⟨?_, ?_, ?_⟩
  · rw [hrange]
    exact hfin
  · rw [hrange]
    calc Module.finrank ℂ (LinearMap.range π) ≤ Module.finrank ℂ (LinearMap.range g) :=
          Submodule.finrank_mono hπg
      _ ≤ Module.finrank ℂ ℂ := LinearMap.finrank_range_le g
      _ = 1 := Module.finrank_self ℂ
  · intro e he
    let lam : Y →ₗ[ℂ] ℂ := (innerSL ℂ e).toLinearMap ∘ₗ Θ ∘ₗ Y.subtype
    have hkerLam : LinearMap.ker q ≤ LinearMap.ker lam := by
      intro y hy
      simp only [LinearMap.mem_ker, q, lam, LinearMap.comp_apply, Submodule.coe_subtype,
        ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hy ⊢
      exact Submodule.inner_left_of_mem_orthogonal (hV y y.2 hy) he.2
    obtain ⟨c, hc⟩ := exists_comp_eq_of_ker_le_scalar q lam hkerLam
    refine ⟨c 1, fun f hf ↦ ?_⟩
    have h1 : c (ℓ f) = ⟪e, Θ f⟫_ℂ := LinearMap.congr_fun hc ⟨f, hf⟩
    have h2 : c (ℓ f) = c 1 * ℓ f := by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [← h1, h2]

/-- `x ^ b (2 (1 + log² x)) ^ c` tends to zero at infinity when `b < 0`. -/
theorem tendsto_rpow_mul_logWeight {b c : ℝ} (hb : b < 0) (hc : 0 ≤ c) :
    Tendsto (fun x : ℝ ↦ x ^ b * (2 * (1 + Real.log x ^ 2)) ^ c) atTop (𝓝 0) := by
  have ho := isLittleO_log_rpow_rpow_atTop (2 * c) (neg_pos.mpr hb)
  have h1 : Tendsto (fun x ↦ Real.log x ^ (2 * c) / x ^ (-b)) atTop (𝓝 0) :=
    ho.tendsto_div_nhds_zero
  have h2 := h1.const_mul (4 ^ c)
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
    have hlog : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hx
    have hl0 : 0 ≤ Real.log x := zero_le_one.trans hlog
    have hbase : 2 * (1 + Real.log x ^ 2) ≤ 4 * Real.log x ^ 2 := by nlinarith
    have hpow : (2 * (1 + Real.log x ^ 2)) ^ c ≤ 4 ^ c * Real.log x ^ (2 * c) := by
      calc (2 * (1 + Real.log x ^ 2)) ^ c ≤ (4 * Real.log x ^ 2) ^ c :=
            Real.rpow_le_rpow (by positivity) hbase hc
        _ = 4 ^ c * Real.log x ^ (2 * c) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hl0,
              Real.rpow_two]
    have hxb : x ^ b = (x ^ (-b))⁻¹ := by rw [Real.rpow_neg hx0.le, inv_inv]
    calc x ^ b * (2 * (1 + Real.log x ^ 2)) ^ c ≤ x ^ b * (4 ^ c * Real.log x ^ (2 * c)) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0.le _)
      _ = 4 ^ c * (Real.log x ^ (2 * c) / x ^ (-b)) := by rw [hxb]; ring

end AbstractOne

section Levels

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientHaarMeasureSec1

local notation "mₛ(" S ")" =>
  (continuousSIdeleQuotientNorm F S : SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "localWMeasure" => (sLocalQuotientTamagawaMeasure F S).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm(mₛ(S)) g)))
local notation "LocalW" => Lp ℂ 2 localWMeasure
local notation "tests(" Λ ")" =>
  sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S Λ)
local notation "fullB(" hs ", " ha ", " ω ", " Λ ")" =>
  sLocalFullPWSobolev (F := F) (S := S) hs ha ω Λ
local notation "levelV(" hs ", " ha ", " ω ", " Λ ")" =>
  sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ

/-- Paper: Proposition 2.3.1.2(1), p. 100. The theta function on classes of the translate of a
test by an S-idele `u` is the theta function of the test translated by the class of `u`. -/
theorem sLocalAdelicThetaOnClasses_unitTranslate (u : (SAdeleRing F S)ˣ) (f : ℬₛ)
    (c : SIdeleQuotient F S) :
    sLocalAdelicThetaOnClasses F S (schwartzBruhatUnitTranslate u f) c =
      sLocalAdelicThetaOnClasses F S f ((QuotientGroup.mk u)⁻¹ * c) := by
  refine QuotientGroup.induction_on c fun g ↦ ?_
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_unitTranslate, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, sLocalAdelicThetaOnClasses_mk]

/-- Paper: Definition 5.2.2.1(2), p. 232. The homogeneous theta function of the translate of a
test by an S-idele `u` is the homogeneous theta function translated by the class of `u`. -/
theorem sLocalHomogeneousAdelicThetaLinearMap_unitTranslate (ω : PontryaginDual J₁)
    (u : (SAdeleRing F S)ˣ) (f : ℬₛ) (c : SIdeleQuotient F S) :
    sLocalHomogeneousAdelicThetaLinearMap F S ω (schwartzBruhatUnitTranslate u f) c =
      sLocalHomogeneousAdelicThetaLinearMap F S ω f ((QuotientGroup.mk u)⁻¹ * c) := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply, sLocalHomogeneousAdelicThetaLinearMap_apply]
  simp only [sLocalAdelicThetaOnClasses_unitTranslate, mul_assoc]

/-- Paper: Proposition 7.3.2.4(3), p. 356, for translates of tests. Translation by an S-idele of
norm at least one preserves the tests of the product region. -/
theorem unitTranslate_mem_sLocalPWTests_of_one_le {u : (SAdeleRing F S)ˣ}
    (hu : 1 ≤ ((sIdeleNorm F S u).val : ℝ)) {Λ : ℝ} {f : ℬₛ} (hf : f ∈ tests(Λ)) :
    schwartzBruhatUnitTranslate u f ∈ tests(Λ) := by
  obtain ⟨h, hh, hband⟩ := (mem_sLocalPWTests le_rfl _ f).mp hf
  rw [levelPolar_transition_self] at hh
  subst hh
  refine (mem_sLocalPWTests le_rfl _ _).mpr
    ⟨schwartzBruhatUnitTranslate u h, levelPolar_transition_self _, ?_⟩
  obtain ⟨b, hb⟩ := levelPolar_translate_fourier u
  let e : Multiplicative (SAdeleRing F S) ≃ₜ Multiplicative (SAdeleRing F S) :=
    { toFun := fun y ↦ Multiplicative.ofAdd ((u : SAdeleRing F S) * y.toAdd)
      invFun := fun y ↦ Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing F S) * y.toAdd)
      left_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  have hreg : ∀ y : SAdeleRing F S, (u : SAdeleRing F S) * y ∈ sLocalPWProductRegion S Λ →
      y ∈ sLocalPWProductRegion S Λ := by
    intro y hy
    change levelPolarProduct ((u : SAdeleRing F S) * y) ≤ Λ at hy
    change levelPolarProduct y ≤ Λ
    rw [levelPolarProduct_mul, levelPolarProduct_unit] at hy
    have h0 : 0 ≤ levelPolarProduct y := by unfold levelPolarProduct; positivity
    nlinarith
  exact levelPolar_translate_support e ((b : ℝ) : ℂ) (sAdeleSchwartzFourier h).val
    (sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u h)).val (fun y ↦ hb h y.toAdd)
    (Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Λ)
    (Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Λ)
    (fun y hy ↦ hreg y.toAdd hy) hband.1 hband.2

/-- `1 + (x + y)² ≤ 2 (1 + x²) (1 + y²)`. -/
theorem one_add_sq_add_le (x y : ℝ) : 1 + (x + y) ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x * y)]

/-- The logarithmic Sobolev density at a product of norms is at most a constant multiple of the
density at the second factor. -/
theorem intervalSobolevDensity_add_le {s : ℝ} (hs : 0 ≤ s) (x y : ℝ) :
    intervalSobolevDensity 0 0 s (x + y) ≤
      (2 * (1 + x ^ 2)) ^ (s / 2) * intervalSobolevDensity 0 0 s y := by
  simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) (by nlinarith [one_add_sq_add_le x y])
    (by positivity)

/-- Paper: (11.2.1.1), p. 487, and Definition 9.3.1.1, p. 419. The full theta class of a
translate of a test by an S-idele `u` has squared norm at most `|u| ^ (2a) 2 ^ (s/2)
(1 + log² |u|) ^ (s/2)` times that of the test. -/
theorem norm_sq_sLocalFullPWThetaSobolevMap_unitTranslate_le (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (u : (SAdeleRing F S)ˣ) (f : ℬₛ) :
    ‖sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω
        (schwartzBruhatUnitTranslate u f)‖ ^ 2 ≤
      ((sIdeleNorm F S u).val : ℝ) ^ (2 * a) *
        (2 * (1 + Real.log ((sIdeleNorm F S u).val : ℝ) ^ 2)) ^ (s / 2) *
          ‖sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f‖ ^ 2 := by
  let μ := sLocalQuotientTamagawaMeasure F S
  let N (c : SIdeleQuotient F S) : ℝ := (((mₛ(S)) c).val : ℝ)
  let w (c : SIdeleQuotient F S) : ℝ := intervalSobolevDensity 0 0 s (Real.log (N c))
  let θ (g : ℬₛ) : SIdeleQuotient F S → ℂ := sLocalHomogeneousAdelicThetaLinearMap F S ω g
  let G (g : ℬₛ) (c : SIdeleQuotient F S) : ℂ := ((N c ^ a : ℝ) : ℂ) * θ g c
  have hN (c) : 0 < N c := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hw (c) : 0 ≤ w c := by
    simp only [w, intervalSobolevDensity]
    positivity
  have hNm : Measurable N :=
    (measurable_coe_nnreal_real).comp ((Units.continuous_val.comp (mₛ(S)).continuous).measurable)
  have hwm : Measurable w := by
    have hd : Measurable (intervalSobolevDensity 0 0 s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact hd.comp (Real.measurable_log.comp hNm)
  have hdm : Measurable fun c ↦ ENNReal.ofReal (w c) := ENNReal.measurable_ofReal.comp hwm
  have hrep (g : ℬₛ) :
      (sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω g : SIdeleQuotient F S → ℂ)
        =ᵐ[localWMeasure] G g :=
    MemLp.coeFn_toLp (sLocalFullPWTheta_memLp (F := F) (S := S) (s := s) ha ω g)
  have hnorm (g : ℬₛ) :
      ‖sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω g‖ ^ 2 =
        ∫ c, w c * ‖G g c‖ ^ 2 ∂μ := by
    calc ‖sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω g‖ ^ 2
        = ∫ c, ‖(sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω g :
            SIdeleQuotient F S → ℂ) c‖ ^ 2 ∂localWMeasure :=
          (L2.integral_sq_norm (𝕜 := ℂ) _).symm
      _ = ∫ c, ‖G g c‖ ^ 2 ∂localWMeasure :=
          integral_congr_ae ((hrep g).mono fun c hc ↦ by simp only [hc])
      _ = ∫ c, w c * ‖G g c‖ ^ 2 ∂μ := by
          rw [integral_withDensity_eq_integral_toReal_smul hdm
            (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
          refine integral_congr_ae (ae_of_all _ fun c ↦ ?_)
          simp only [ENNReal.toReal_ofReal (hw c), smul_eq_mul]
  have hint (g : ℬₛ) : Integrable (fun c ↦ w c * ‖G g c‖ ^ 2) μ := by
    have hmem := sLocalFullPWTheta_memLp (F := F) (S := S) (s := s) ha ω g
    have h1 := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    have h2 := (integrable_withDensity_iff_integrable_smul' hdm
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).1 h1
    refine h2.congr (ae_of_all _ fun c ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hw c), smul_eq_mul]
    rfl
  let t := ((sIdeleNorm F S u).val : ℝ)
  have ht : 0 < t := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hNmul (c : SIdeleQuotient F S) : N (QuotientGroup.mk u * c) = t * N c := by
    simp only [N, map_mul, Units.val_mul, NNReal.coe_mul]
    rfl
  have hshift : (∫ c, w c * ‖G (schwartzBruhatUnitTranslate u f) c‖ ^ 2 ∂μ) =
      ∫ c, w (QuotientGroup.mk u * c) *
        ‖G (schwartzBruhatUnitTranslate u f) (QuotientGroup.mk u * c)‖ ^ 2 ∂μ :=
    (integral_mul_left_eq_self (fun c ↦ w c * ‖G (schwartzBruhatUnitTranslate u f) c‖ ^ 2)
      (QuotientGroup.mk u)).symm
  have hpt (c : SIdeleQuotient F S) :
      w (QuotientGroup.mk u * c) *
          ‖G (schwartzBruhatUnitTranslate u f) (QuotientGroup.mk u * c)‖ ^ 2 ≤
        t ^ (2 * a) * (2 * (1 + Real.log t ^ 2)) ^ (s / 2) * (w c * ‖G f c‖ ^ 2) := by
    have hθ : θ (schwartzBruhatUnitTranslate u f) (QuotientGroup.mk u * c) = θ f c := by
      simp only [θ, sLocalHomogeneousAdelicThetaLinearMap_unitTranslate, inv_mul_cancel_left]
    have hG : ‖G (schwartzBruhatUnitTranslate u f) (QuotientGroup.mk u * c)‖ ^ 2 =
        t ^ (2 * a) * ‖G f c‖ ^ 2 := by
      simp only [G, hθ, hNmul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht.le a),
        abs_of_nonneg (Real.rpow_nonneg (hN c).le a), mul_pow,
        Real.mul_rpow ht.le (hN c).le]
      rw [show t ^ (2 * a) = (t ^ a) ^ 2 by rw [mul_comm, Real.rpow_mul ht.le, Real.rpow_two]]
      ring
    have hW : w (QuotientGroup.mk u * c) ≤ (2 * (1 + Real.log t ^ 2)) ^ (s / 2) * w c := by
      simp only [w, hNmul, Real.log_mul ht.ne' (hN c).ne']
      exact intervalSobolevDensity_add_le hs _ _
    rw [hG]
    have h0 : 0 ≤ ‖G f c‖ ^ 2 := by positivity
    have h1 : 0 ≤ t ^ (2 * a) := Real.rpow_nonneg ht.le _
    calc w (QuotientGroup.mk u * c) * (t ^ (2 * a) * ‖G f c‖ ^ 2)
        ≤ ((2 * (1 + Real.log t ^ 2)) ^ (s / 2) * w c) * (t ^ (2 * a) * ‖G f c‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hW (mul_nonneg h1 h0)
      _ = _ := by ring
  rw [hnorm, hnorm, hshift, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun c ↦ mul_nonneg (hw _) (by positivity))
    ((hint f).const_mul _) (ae_of_all _ hpt)

attribute [local instance] completeSpace_sLocalFullPWSobolev
  completeSpace_sLocalInvariantPWSobolev

set_option maxHeartbeats 1600000 in
/-- Paper: Definition 11.2.1.3(1), p. 488, with Theorem 12.4.1.1, Step III, p. 517.
Reconstruction: at a twist `0 < a < 1`, the full theta class of every test of the product region
that vanishes at zero lies in the polar-free level. The integral condition is lost in the closure:
dilating a test by an S-idele of norm `N` keeps its integral, divides its value at zero by `N`,
and multiplies its weighted norm by at most `N ^ (a - 1)` times a power of `log N`. -/
theorem sLocalFullPWThetaSobolevMap_mem_level_of_eval_zero (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (ω : PontryaginDual J₁) (Λ : ℝ) {f : ℬₛ} (hf : f ∈ tests(Λ))
    (hf0 : f (Multiplicative.ofAdd 0) = 0) :
    sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ levelV(hs, ha, ω, Λ) := by
  let Θ := sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω
  let p := sAdelePolarValuesMap (F := F) (S := S)
  have hVc : IsClosed (levelV(hs, ha, ω, Λ) : Set LocalW) :=
    Submodule.isClosed_topologicalClosure _
  have hsub : ∀ g ∈ tests(Λ), p g = 0 → Θ g ∈ levelV(hs, ha, ω, Λ) := fun g hg hp ↦
    sLocalInvariantPWSobolev_mem hs ha ω Λ ⟨g, hp⟩ hg
  by_cases hk : ∃ k ∈ tests(Λ), k (Multiplicative.ofAdd 0) = 0 ∧
      sAdeleSchwartzFourier k (Multiplicative.ofAdd 0) ≠ 0
  swap
  · push Not at hk
    refine hsub f hf ?_
    rw [sAdelePolarValuesMap_apply, hf0, hk f hf hf0]
    rfl
  obtain ⟨k, hk, hk0, hkF⟩ := hk
  let c := sAdeleSchwartzFourier k (Multiplicative.ofAdd 0)
  let k₁ := c⁻¹ • k
  have hk₁ : k₁ ∈ tests(Λ) := Submodule.smul_mem _ _ hk
  have hpk : p k = (0, c) := by rw [sAdelePolarValuesMap_apply, hk0]
  have hpk₁ : p k₁ = (0, 1) := by
    change p (c⁻¹ • k) = _
    rw [map_smul, hpk, Prod.smul_mk, smul_zero, smul_eq_mul, inv_mul_cancel₀ hkF]
  obtain ⟨τ, hτ⟩ := levelDilation_exists_normSection (F := F) (S := S)
  let T (n : ℕ) : ℝ≥0ˣ := Units.mk0 ((n : ℝ≥0) + 1) (by positivity)
  let u (n : ℕ) := τ (T n)
  have hNu (n : ℕ) : ((sIdeleNorm F S (u n)).val : ℝ) = (n : ℝ) + 1 := by
    simp only [u, hτ (T n), T, Units.val_mk0, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  have hNu1 (n : ℕ) : 1 ≤ ((sIdeleNorm F S (u n)).val : ℝ) := by
    rw [hNu]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hptr (n : ℕ) : p (schwartzBruhatUnitTranslate (u n) k₁) = (0, (n : ℂ) + 1) := by
    have h0 : (schwartzBruhatUnitTranslate (u n) k₁) (Multiplicative.ofAdd 0) = 0 := by
      rw [schwartzBruhatUnitTranslate_apply, mul_zero]
      exact congrArg Prod.fst hpk₁
    have h1 : sAdeleSchwartzFourier k₁ (Multiplicative.ofAdd 0) = 1 := congrArg Prod.snd hpk₁
    rw [sAdelePolarValuesMap_apply, h0, sAdeleSchwartzFourier_unitTranslate_zero, h1, hNu]
    push_cast
    ring_nf
  let A := sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)
  let h (n : ℕ) : ℬₛ := (A / ((n : ℂ) + 1)) • schwartzBruhatUnitTranslate (u n) k₁
  have hn1 (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hmem (n : ℕ) : f - h n ∈ tests(Λ) ∧ p (f - h n) = 0 := by
    refine ⟨Submodule.sub_mem _ hf (Submodule.smul_mem _ _
      (unitTranslate_mem_sLocalPWTests_of_one_le (hNu1 n) hk₁)), ?_⟩
    have hpf : p f = (0, A) := by rw [sAdelePolarValuesMap_apply, hf0]
    rw [map_sub, map_smul, hptr, hpf, Prod.smul_mk, smul_zero, smul_eq_mul,
      div_mul_cancel₀ _ (hn1 n), sub_self]
  have hbound (n : ℕ) : ‖Θ (h n)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖Θ k₁‖ ^ 2 *
      (((n : ℝ) + 1) ^ (2 * a - 2) * (2 * (1 + Real.log ((n : ℝ) + 1) ^ 2)) ^ (s / 2)) := by
    have hN := norm_sq_sLocalFullPWThetaSobolevMap_unitTranslate_le hs ha ω (u n) k₁
    rw [hNu] at hN
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsplit : ((n : ℝ) + 1) ^ (2 * a - 2) = ((n : ℝ) + 1) ^ (2 * a) / ((n : ℝ) + 1) ^ 2 := by
      rw [Real.rpow_sub hpos, Real.rpow_two]
    have hc1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg hpos.le]
    have hnorm1 : ‖Θ (h n)‖ = ‖A‖ / ((n : ℝ) + 1) *
        ‖Θ (schwartzBruhatUnitTranslate (u n) k₁)‖ := by
      change ‖Θ ((A / ((n : ℂ) + 1)) • schwartzBruhatUnitTranslate (u n) k₁)‖ = _
      rw [map_smul, norm_smul, norm_div, hc1]
    have hnorm : ‖Θ (h n)‖ ^ 2 = ‖A‖ ^ 2 / ((n : ℝ) + 1) ^ 2 *
        ‖Θ (schwartzBruhatUnitTranslate (u n) k₁)‖ ^ 2 := by
      rw [hnorm1, mul_pow, div_pow]
    rw [hnorm, hsplit]
    have hA : 0 ≤ ‖A‖ ^ 2 / ((n : ℝ) + 1) ^ 2 := by positivity
    calc ‖A‖ ^ 2 / ((n : ℝ) + 1) ^ 2 * ‖Θ (schwartzBruhatUnitTranslate (u n) k₁)‖ ^ 2
        ≤ ‖A‖ ^ 2 / ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1) ^ (2 * a) *
            (2 * (1 + Real.log ((n : ℝ) + 1) ^ 2)) ^ (s / 2) * ‖Θ k₁‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hN hA
      _ = _ := by field_simp
  have hlimR := tendsto_rpow_mul_logWeight (b := 2 * a - 2) (c := s / 2) (by linarith)
    (by positivity)
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ ↦ ‖Θ (h n)‖ ^ 2) atTop (𝓝 0) := by
    have h2 := (hlimR.comp hnat).const_mul (‖A‖ ^ 2 * ‖Θ k₁‖ ^ 2)
    rw [mul_zero] at h2
    exact squeeze_zero (fun n ↦ by positivity) hbound h2
  have hlim : Tendsto (fun n : ℕ ↦ Θ (h n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h3 := hsq.sqrt
    rw [Real.sqrt_zero] at h3
    exact h3.congr fun n ↦ Real.sqrt_sq (norm_nonneg _)
  have hconv : Tendsto (fun n : ℕ ↦ Θ (f - h n)) atTop (𝓝 (Θ f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero] at hlim
    refine hlim.congr fun n ↦ ?_
    rw [map_sub, sub_sub_cancel_left, norm_neg]
  exact hVc.mem_of_tendsto hconv (Eventually.of_forall fun n ↦ hsub _ (hmem n).1 (hmem n).2)

/-- Paper: Definition 11.2.1.3(1), p. 488, with Theorem 12.4.1.1, Step III, p. 517, and the
proof of Theorem 12.5.1.1, p. 520.
Reconstruction: at a twist `0 < a < 1`, in particular at the twist `1/2` of §12.5, the polar-free
level has codimension at most one in the full band, for every number field and every finite set
of places. Each vector of the complement represents a multiple of the value at zero alone. So the
polar term of `sLocalLevel_trace_asymptotic_of_full_comparison` is a single diagonal entry, and
the level removes at most one of the two polar directions that the proof of Theorem 12.5.1.1 on
p. 520 subtracts. -/
theorem sLocalPWSobolev_polarComplement_le_one (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ω : PontryaginDual J₁) (Λ : ℝ) :
    FiniteDimensional ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ) ∧
      Module.finrank ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ) ≤ 1 ∧
      ∀ e ∈ fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ, ∃ c₀ : ℂ, ∀ f ∈ tests(Λ),
        ⟪e, sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f⟫_ℂ =
          c₀ * f (Multiplicative.ofAdd 0) :=
  finrank_inf_orthogonal_le_one (sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω)
    (tests(Λ)) (LinearMap.fst ℂ ℂ ℂ ∘ₗ sAdelePolarValuesMap (F := F) (S := S))
    (fullB(hs, ha, ω, Λ)) (levelV(hs, ha, ω, Λ)) rfl
    (fun _f hf h0 ↦ sLocalFullPWThetaSobolevMap_mem_level_of_eval_zero hs ha ha1 ω Λ hf h0)
    (sLocalPWSobolev_polarComplement hs ha ω Λ).1

end Levels

end RiemannMasullo.Isolated
