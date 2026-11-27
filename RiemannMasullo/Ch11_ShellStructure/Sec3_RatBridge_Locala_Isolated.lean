module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_PV_Isolated
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Local theory at the primes of the conductor: Fourier support

Workstream B for #7351, stage 3, part a: the local factors `χ_q⁻¹ · 1_{ℤ_q^×}` of the Dirichlet
test of stage 1 and its membership in the absolute Paley–Wiener level of (11.3.1.3), p. 494.

* `ratLocalFourier_eq_zero_of_translate`: a function on `ℚ_q` invariant under translation by
  `q^e ℤ_q` has Fourier transform supported in `{|ξ|_q ≤ q^e}`.
* `ratDirichletLocalChar_eq_one`: the local component `c_q` of `ψ` is trivial on
  `1 + q^{e_q} ℤ_q`, `e_q = v_q(N)`; `exists_ratDirichletLocalChar_ne_one`: by primitivity it is
  not trivial on `1 + q^{e_q - 1} ℤ_q`, so its conductor is exactly `q^{e_q}`.
* `unitCharTest_fourier_support`: the factor `c_q⁻¹ · 1_{ℤ_q^×}` has Fourier support in
  `{|ξ|_q ≤ q^{e_q}}`, and `integral_unitCharTestFun`: its integral vanishes.
* `dirTest_mem_absolutePWTests`: the Dirichlet test of a real test with Fourier support in
  `[-X, X]`, `X ≥ max_{q ∣ N} q^{e_q}`, lies in `primaryDivisorialAbsolutePWTests ℚ S X`,
  polarity included.

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal ENNReal SchwartzMap FourierTransform NumberField.AdeleRing TensorProduct
  Pointwise

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

open NumberFieldKB.Chebotarev.RatIdele

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ι" => IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ
local notation "realCoord" =>
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "ν𝔭(" v ")" => finiteLocalAdditiveTamagawaMeasure ℚ v
local notation "μ𝔭(" v ")" => finiteLocalMultiplicativeTamagawaMeasure ℚ v
local notation "ψ𝔭(" v ")" => finiteLocalStandardCharacter ℚ v

local instance (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _
local instance : MeasurableSpace (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace ℚ) → w.Completion))
local instance (v : Vℚ) : MeasurableSpace (v.adicCompletion ℚ) := borel _
local instance (v : Vℚ) : MeasurableSpace (v.adicCompletion ℚ)ˣ := borel _
local instance (S : Finset Vℚ) : MeasurableSpace (SAdeleRing ℚ S) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing ℚ × ((v : S) → v.val.adicCompletion ℚ)))
local instance (v : Vℚ) : LocallyCompactSpace (v.adicCompletion ℚ) :=
  letI : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion v
  inferInstance
local instance (v : Vℚ) : LocallyCompactSpace (v.adicCompletion ℚ)ˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion ℚ)).locallyCompactSpace

/-! ### Scaling the local additive measure by a unit (re-derived from `AppB_AnalyticNT/Sec4b`) -/

section LocalScaling

private theorem ratLocal_distribHaarChar (v : Vℚ) (w : (v.adicCompletion ℚ)ˣ) :
    distribHaarChar (v.adicCompletion ℚ) w = ‖w.val‖₊ := by
  let K := v.adicCompletion ℚ
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  let ν : Measure K := ν𝔭(v)
  let : ν.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v
  let : ν.Regular := finiteLocalAdditiveTamagawaMeasure_regular ℚ v
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar ℚ v
  have he := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let C : ENNReal := (v.asIdeal.absNorm : ENNReal) / ((v.asIdeal.absNorm : ENNReal) - 1)
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hC0 : C ≠ 0 := ENNReal.div_ne_zero.mpr ⟨(zero_lt_one.trans hq).ne',
    ENNReal.sub_ne_top (ENNReal.natCast_ne_top _)⟩
  have hCtop : C ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt hq).ne'
  have hmass (A : Set K) (hA : MeasurableSet A) (h0 : (0 : K) ∉ A) :
      μ𝔭(v) (Units.val ⁻¹' A) = C * ∫⁻ x in A, (↑‖x‖₊ : ENNReal)⁻¹ ∂ν := by
    have hsub : A ⊆ range (Units.val : Kˣ → K) := fun x hx ↦
      ⟨Units.mk0 x (fun h ↦ h0 (h ▸ hx)), rfl⟩
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, smul_apply, smul_eq_mul,
      he.comap_apply, image_preimage_eq_of_subset hsub, withDensity_apply _ hA]
  let S : Set K := Metric.sphere 0 1
  have hSo : IsOpen S := IsUltrametricDist.isOpen_sphere (0 : K) one_ne_zero
  have hS0 : (0 : K) ∉ S := by simp [S]
  have hSν0 : ν S ≠ 0 := (hSo.measure_pos ν ⟨1, by simp [S]⟩).ne'
  have hSνtop : ν S ≠ ⊤ := (isCompact_sphere (0 : K) 1).measure_lt_top.ne
  have hwS : w • S = Metric.sphere 0 ‖w.val‖ := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem, Units.smul_def, mem_sphere_zero_iff_norm,
      mem_sphere_zero_iff_norm, smul_eq_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      inv_mul_eq_one₀ (norm_ne_zero_iff.mpr w.ne_zero), eq_comm]
  have hwSm : MeasurableSet (w • S) := hSo.measurableSet.const_smul w
  have hw0 : (0 : K) ∉ w • S := by
    rw [hwS, mem_sphere_zero_iff_norm, norm_zero]
    exact (norm_pos_iff.mpr w.ne_zero).ne
  have hwn : (↑‖w.val‖₊ : ENNReal) ≠ 0 := by simp [w.ne_zero]
  apply distribHaarChar_eq_of_measure_smul_eq_mul hSν0 hSνtop
  have hinv : μ𝔭(v) (Units.val ⁻¹' (w • S)) = μ𝔭(v) (Units.val ⁻¹' S) := by
    have hpre : Units.val ⁻¹' (w • S) = (fun u ↦ w⁻¹ * u) ⁻¹' (Units.val ⁻¹' S) := by
      ext u
      simp only [mem_preimage, Units.val_mul, Units.smul_def]
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ w.ne_zero, smul_eq_mul, Units.val_inv_eq_inv_val]
    rw [hpre, measure_preimage_mul]
  rw [hmass _ hwSm hw0, hmass _ hSo.measurableSet hS0,
    setLIntegral_congr_fun hwSm (g := fun _ ↦ (↑‖w.val‖₊ : ENNReal)⁻¹) (fun x hx ↦ by
      rw [hwS, mem_sphere_zero_iff_norm] at hx
      simp only [show ‖x‖₊ = ‖w.val‖₊ from NNReal.eq hx]),
    setLIntegral_congr_fun hSo.measurableSet (g := fun _ ↦ (1 : ENNReal)) (fun x hx ↦ by
      rw [mem_sphere_zero_iff_norm] at hx
      simp [show ‖x‖₊ = 1 from NNReal.eq hx]),
    setLIntegral_const, setLIntegral_const, one_mul] at hinv
  have h := (ENNReal.mul_right_inj hC0 hCtop).mp hinv
  calc ν (w • S) = ↑‖w.val‖₊ * ((↑‖w.val‖₊ : ENNReal)⁻¹ * ν (w • S)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hwn ENNReal.coe_ne_top, one_mul]
    _ = _ := by rw [h]

/-- Multiplication by a unit pushes the local additive Tamagawa measure forward to its multiple
by the inverse norm. -/
theorem ratLocal_map_mul (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ) :
    (ν𝔭(v)).map (u.val * ·) = ENNReal.ofReal ‖u.val‖⁻¹ • ν𝔭(v) := by
  let K := v.adicCompletion ℚ
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := ν𝔭(v)
  let : ν.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v
  let : ν.Regular := finiteLocalAdditiveTamagawaMeasure_regular ℚ v
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, smul_apply, smul_eq_mul]
  have hpre : (u.val * ·) ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [mem_preimage, Set.mem_inv_smul_set_iff]
    rfl
  rw [hpre, ← distribHaarChar_mul, ratLocal_distribHaarChar, Units.val_inv_eq_inv_val,
    nnNorm_inv, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, coe_nnNorm]

/-- Integrals against the local additive measure are invariant under multiplication by a unit
of norm one. -/
theorem ratLocal_integral_comp_mul (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ)
    (hu : ‖u.val‖ = 1) (h : v.adicCompletion ℚ → ℂ) :
    (∫ y, h (u.val * y) ∂ν𝔭(v)) = ∫ z, h z ∂ν𝔭(v) := by
  let : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  let e := (Homeomorph.mulLeft₀ u.val u.ne_zero).toMeasurableEquiv
  calc (∫ y, h (u.val * y) ∂ν𝔭(v)) = ∫ y, h (e y) ∂ν𝔭(v) := rfl
    _ = ∫ z, h z ∂((ν𝔭(v)).map e) := (integral_map_equiv e h).symm
    _ = _ := by
      rw [show ⇑e = (u.val * · : _ → _) from rfl, ratLocal_map_mul, hu, inv_one,
        ENNReal.ofReal_one, one_smul]

end LocalScaling

/-! ### The S-local Fourier transform of a product test -/

section FourierProduct

/-- The archimedean part of the standard character of `ℚ`. -/
def ratArchChar (z : InfiniteAdeleRing ℚ) : Circle :=
  sAdeleStandardCharacter ℚ ∅ (z, fun w ↦ absurd w.2 (Finset.notMem_empty _))

/-- The archimedean Fourier transform of `ℚ`, with the Tamagawa measure and standard character. -/
def ratArchFourier (A : InfiniteAdeleRing ℚ → ℂ) (η : InfiniteAdeleRing ℚ) : ℂ :=
  ∫ z : InfiniteAdeleRing ℚ, A z * star (ratArchChar (z * η) : ℂ)
    ∂(show Measure (InfiniteAdeleRing ℚ) from Measure.pi (infiniteLocalAdditiveTamagawaMeasure ℚ))

private theorem sAdeleStandardCharacter_split (S : Finset Vℚ) (a : SAdeleRing ℚ S) :
    sAdeleStandardCharacter ℚ S a = ratArchChar a.1 * ∏ v : S, ψ𝔭(v.val) (a.2 v) := by
  rw [ratArchChar, sAdeleStandardCharacter, sAdeleStandardCharacter,
    Finset.univ_eq_empty (α := ↥(∅ : Finset Vℚ)), Finset.prod_empty, mul_one]

/-- The S-local Fourier transform of a product test is the product of the archimedean and the
local Fourier transforms. -/
theorem ratSLocalFourier_prod (S : Finset Vℚ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S)))
    (A : InfiniteAdeleRing ℚ → ℂ) (b : (v : S) → v.val.adicCompletion ℚ → ℂ)
    (hf : ∀ x : SAdeleRing ℚ S, f (Multiplicative.ofAdd x) = A x.1 * ∏ v, b v (x.2 v))
    (y : SAdeleRing ℚ S) :
    sAdeleSchwartzFourier f (Multiplicative.ofAdd y) =
      ratArchFourier A y.1 * ∏ v, tamagawaFourier ν𝔭(v.val) ψ𝔭(v.val) (b v) (y.2 v) := by
  classical
  let (v : S) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let (w : InfinitePlace ℚ) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion ℚ) := ⟨rfl⟩
  let (w : InfinitePlace ℚ) : (infiniteLocalAdditiveTamagawaMeasure ℚ w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar ℚ w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure ℚ v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v.val
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let μa := infiniteLocalAdditiveTamagawaMeasure ℚ
  let μb := fun v : S ↦ finiteLocalAdditiveTamagawaMeasure ℚ v.val
  let B (v : S) (x : v.val.adicCompletion ℚ) := b v x * star (ψ𝔭(v.val) (x * y.2 v) : ℂ)
  have he (x : SAdeleRing ℚ S) :
      f (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter ℚ S (x * y) : ℂ) =
        (A x.1 * star (ratArchChar (x.1 * y.1) : ℂ)) * ∏ v, B v (x.2 v) := by
    rw [hf, sAdeleStandardCharacter_split]
    let C := (starRingEnd ℂ).toMonoidHom.comp Circle.coeHom
    change _ * C (ratArchChar (x.1 * y.1) * ∏ v : S, ψ𝔭(v.val) (x.2 v * y.2 v)) =
      (A x.1 * C (ratArchChar (x.1 * y.1))) * ∏ v, b v (x.2 v) * C (ψ𝔭(v.val) (x.2 v * y.2 v))
    rw [map_mul, map_prod, Finset.prod_mul_distrib]
    ring
  change (∫ x : SAdeleRing ℚ S, f (Multiplicative.ofAdd x) *
      star (sAdeleStandardCharacter ℚ S (x * y) : ℂ) ∂(Measure.pi μa).prod (Measure.pi μb)) =
    (∫ z : InfiniteAdeleRing ℚ, A z * star (ratArchChar (z * y.1) : ℂ)
      ∂(show Measure (InfiniteAdeleRing ℚ) from Measure.pi μa)) * ∏ v, ∫ x, B v x ∂μb v
  simp_rw [he]
  exact (integral_prod_mul (μ := Measure.pi μa) (ν := Measure.pi μb)
    (fun z : InfiniteAdeleRing ℚ ↦ A z * star (ratArchChar (z * y.1) : ℂ))
    (fun p ↦ ∏ v, B v (p v))).trans
    (congrArg _ (integral_fintype_prod_eq_prod B))

/-- The archimedean Fourier transform of a real test is its real Fourier transform. -/
theorem ratArchFourier_archTest (f : 𝓢(ℝ, ℂ)) (η : InfiniteAdeleRing ℚ) :
    ratArchFourier (fun z ↦ f (realCoord (z Rat.infinitePlace))) η =
      𝓕 f (realCoord (η Rat.infinitePlace)) := by
  let e := (sAdeleSchwartz_inductiveTensor_equiv ℚ ∅).choose
  let g : (w : (∅ : Finset Vℚ)) → SchwartzBruhat (Multiplicative (w.val.adicCompletion ℚ)) :=
    fun w ↦ absurd w.2 (Finset.notMem_empty _)
  let f₀ := e (archTest f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))
  have hf₀ (x : SAdeleRing ℚ ∅) : f₀ (Multiplicative.ofAdd x) =
      f (realCoord (x.1 Rat.infinitePlace)) := by
    rw [(sAdeleSchwartz_inductiveTensor_equiv ℚ ∅).choose_spec, archTest_apply,
      Finset.univ_eq_empty (α := ↥(∅ : Finset Vℚ)), Finset.prod_empty, mul_one]
  let y : SAdeleRing ℚ ∅ := (η, fun w ↦ absurd w.2 (Finset.notMem_empty _))
  have h1 := ratSLocalFourier_prod ∅ f₀ (fun z ↦ f (realCoord (z Rat.infinitePlace)))
    (fun w ↦ absurd w.2 (Finset.notMem_empty _))
    (fun x ↦ by rw [hf₀, Finset.univ_eq_empty (α := ↥(∅ : Finset Vℚ)), Finset.prod_empty,
      mul_one]) y
  rw [Finset.univ_eq_empty (α := ↥(∅ : Finset Vℚ)), Finset.prod_empty, mul_one] at h1
  exact h1.symm.trans (sAdeleSchwartzFourier_ratEmpty_apply f f₀ hf₀ y)

end FourierProduct


/-! ### Fourier support from translation invariance -/

section LocalSupport

/-- `|p|_p = p⁻¹`. -/
theorem ratPrime_norm (v : Vℚ) : ‖(pr v : v.adicCompletion ℚ)‖ = (pr v : ℝ)⁻¹ := by
  rw [norm_uniformizer_adicCompletion v _ (ratPrime_isUniformizer v), absNorm_asIdeal]

private theorem ratLocalChar_add (v : Vℚ) (x y : v.adicCompletion ℚ) :
    ψ𝔭(v) (x + y) = ψ𝔭(v) x * ψ𝔭(v) y := by
  obtain ⟨ψ, hψ, -⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom ℚ v
  rw [← hψ, ← hψ, ← hψ, ofAdd_add, map_mul]

/-- Over `ℚ` the different is trivial, so the annihilator of `ℤ_p` is `ℤ_p`: a frequency of norm
greater than one pairs nontrivially with some `p`-adic integer. -/
private theorem ratLocalChar_exists_ne_one (v : Vℚ) (ξ : v.adicCompletion ℚ) (hξ : 1 < ‖ξ‖) :
    ∃ b ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)), ψ𝔭(v) (b * ξ) ≠ 1 := by
  by_contra! h
  have hd : differentIdeal ℤ (𝓞 ℚ) = 1 := by
    rw [Ideal.one_eq_top, ← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ),
      NumberField.discr_rat]
    rfl
  have hmem : ξ ∈ {y : v.adicCompletion ℚ | ∀ x ∈ (v.adicCompletionIntegers ℚ :
      Set (v.adicCompletion ℚ)), ψ𝔭(v) (x * y) = 1} := h
  rw [finiteLocalStandardCharacter_annihilator_integers, hd, multiplicity_one_right, pow_zero,
    Set.mem_ofPred_eq] at hmem
  exact absurd hmem (not_le.mpr hξ)

/-- Paper: (11.3.1.3), p. 494, local input at `q ∣ N`.
**Fourier support from translation invariance.** A function on `ℚ_p` invariant under translation
by `p^e ℤ_p` has Fourier transform (Tamagawa measure, standard character) vanishing at every
frequency of norm greater than `p^e`. -/
theorem ratLocalFourier_eq_zero_of_translate (v : Vℚ) (e : ℕ) (f : v.adicCompletion ℚ → ℂ)
    (hf : ∀ x b, b ∈ v.adicCompletionIntegers ℚ →
      f (x + (pr v : v.adicCompletion ℚ) ^ e * b) = f x)
    (ξ : v.adicCompletion ℚ) (hξ : (pr v : ℝ) ^ e < ‖ξ‖) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v) f ξ = 0 := by
  let : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v
  have hpos : (0 : ℝ) < (pr v : ℝ) ^ e := pow_pos (by exact_mod_cast (pr_prime v).pos) e
  have hp : ‖(pr v : v.adicCompletion ℚ) ^ e‖ = ((pr v : ℝ) ^ e)⁻¹ := by
    rw [norm_pow, ratPrime_norm, inv_pow]
  obtain ⟨b, hb, hne⟩ := ratLocalChar_exists_ne_one v ((pr v : v.adicCompletion ℚ) ^ e * ξ)
    (by rw [norm_mul, hp]; exact (one_lt_inv_mul₀ hpos).mpr hξ)
  set a := (pr v : v.adicCompletion ℚ) ^ e * b with ha
  have hs : star (ψ𝔭(v) (a * ξ) : ℂ) ≠ 1 := by
    rw [show a * ξ = b * ((pr v : v.adicCompletion ℚ) ^ e * ξ) by rw [ha]; ring]
    intro h1
    rw [show star (ψ𝔭(v) (b * ((pr v : v.adicCompletion ℚ) ^ e * ξ)) : ℂ) =
      ((ψ𝔭(v) (b * ((pr v : v.adicCompletion ℚ) ^ e * ξ)))⁻¹ : Circle) from
        (Circle.coe_inv_eq_conj _).symm] at h1
    exact hne (inv_eq_one.mp (Circle.coe_eq_one.mp h1))
  have hshift : tamagawaFourier ν𝔭(v) ψ𝔭(v) f ξ =
      star (ψ𝔭(v) (a * ξ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) f ξ := by
    unfold tamagawaFourier
    rw [← integral_const_mul]
    have h := integral_add_left_eq_self (μ := ν𝔭(v))
      (fun x ↦ f x * star (ψ𝔭(v) (x * ξ) : ℂ)) a
    rw [← h]
    congr 1
    funext x
    rw [show a + x = x + (pr v : v.adicCompletion ℚ) ^ e * b by rw [ha]; ring, hf x b hb,
      show (x + (pr v : v.adicCompletion ℚ) ^ e * b) * ξ = a * ξ + x * ξ by rw [ha]; ring,
      ratLocalChar_add, Circle.coe_mul, star_mul']
    ring
  by_contra hF
  exact hs ((mul_eq_right₀ hF).mp hshift.symm)

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **The local component of `ψ` is trivial on `1 + q^{e_q} ℤ_q`**, `e_q = v_q(N)` (at a place
`p ∤ N`, where `e = 0`, on all of `ℤ_p^×`). -/
theorem ratDirichletLocalChar_eq_one (hχ : χ.IsPrimitive) (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1)
    (hc : Valued.v (((u : v.adicCompletion ℚ) - 1) /
      (pr v : v.adicCompletion ℚ) ^ N.factorization (pr v)) ≤ 1) :
    ratDirichletLocalChar hχ v u = 1 := by
  rw [ratDirichletLocalChar_apply]
  have hrat : ratPart (ι v u) = 1 := by
    have h := ratPart_ofAdicCompletion v u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
    rwa [zpow_zero] at h
  have hunit : unitPart (ι v u) = ι v u := by
    rw [unitPart_apply, hrat, map_one, inv_one, mul_one]
  have hres : resMod N (ι v u) = 1 := by
    refine resMod_eq_one_of N fun p ↦ ?_
    rw [hunit]
    by_cases hpv : placeP N p = v
    · subst hpv
      rw [compV_ofAdicCompletion_self]
      apply redP_eq_one
      rw [pr_placeOf] at hc
      exact hc
    · rw [compV_ofAdicCompletion_ne hpv, Units.val_one, redP_one]
  have h1 : (resMod N).toHomUnits (ι v u) = 1 := Units.ext (by simp [hres])
  rw [coe_ideleChar, h1, map_one, Units.val_one, inv_one]

private theorem mem_unitsImage_iff (v : Vℚ) (y : v.adicCompletion ℚ) :
    y ∈ Units.val '' ((v.adicCompletionIntegers ℚ).units : Set (v.adicCompletion ℚ)ˣ) ↔
      Valued.v y = 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hw
  · intro hy
    have hy0 : y ≠ 0 := fun h ↦ by rw [h, map_zero] at hy; exact zero_ne_one hy
    exact ⟨Units.mk0 y hy0,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hy, rfl⟩

private theorem valued_add_eq_one_iff (v : Vℚ) (x a : v.adicCompletion ℚ)
    (ha : Valued.v a < 1) : Valued.v (x + a) = 1 ↔ Valued.v x = 1 := by
  constructor
  · intro h
    have hna : Valued.v (-a) < Valued.v (x + a) := by rw [Valuation.map_neg, h]; exact ha
    rw [show x = (x + a) + -a by ring, Valuation.map_add_eq_of_lt_left _ hna, h]
  · intro h
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [h]; exact ha), h]

/-- For `q ∣ N`, the factor `c_q⁻¹ · 1_{ℤ_q^×}` is invariant under translation by
`q^{e_q} ℤ_q`. -/
theorem unitCharTestFun_translate (hχ : χ.IsPrimitive) (v : Vℚ) (hv : pr v ∣ N)
    (x b : v.adicCompletion ℚ) (hb : b ∈ v.adicCompletionIntegers ℚ) :
    unitCharTestFun v (ratDirichletLocalChar hχ v)
        (x + (pr v : v.adicCompletion ℚ) ^ N.factorization (pr v) * b) =
      unitCharTestFun v (ratDirichletLocalChar hχ v) x := by
  set e := N.factorization (pr v)
  have he : 1 ≤ e := (pr_prime v).factorization_pos_of_dvd (NeZero.ne N) hv
  set π := (pr v : v.adicCompletion ℚ)
  have hπ : Valued.v π < 1 := by
    have h : Valued.v π = WithZero.exp (-1) := by
      simpa only [Rat.cast_natCast, eq_self, ↓reduceIte] using valued_prime v (pr_prime v)
    rw [h]; exact WithZero.exp_lt_one_iff.mpr (by norm_num)
  have hπ0 : π ≠ 0 := (ratPrime_isUniformizer v).ne_zero
  have hb1 : Valued.v b ≤ 1 := by
    have h := hb
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have ha : Valued.v (π ^ e * b) < 1 := by
    rw [map_mul, map_pow]
    calc Valued.v π ^ e * Valued.v b ≤ Valued.v π ^ e := mul_le_of_le_one_right zero_le hb1
      _ ≤ Valued.v π := pow_le_of_le_one zero_le hπ.le (by omega)
      _ < 1 := hπ
  unfold unitCharTestFun
  by_cases hx : Valued.v x = 1
  · have hxa : Valued.v (x + π ^ e * b) = 1 := (valued_add_eq_one_iff v x _ ha).mpr hx
    have hx0 : x ≠ 0 := fun h ↦ by rw [h, map_zero] at hx; exact zero_ne_one hx
    have hxa0 : x + π ^ e * b ≠ 0 := fun h ↦ by rw [h, map_zero] at hxa; exact zero_ne_one hxa
    rw [Set.indicator_of_mem ((mem_unitsImage_iff v _).mpr hxa),
      Set.indicator_of_mem ((mem_unitsImage_iff v _).mpr hx)]
    simp only [ne_eq, hx0, hxa0, not_false_eq_true, ↓reduceDIte]
    have hu1 : Valued.v (1 + π ^ e * b / x) = 1 := by
      rw [valued_add_eq_one_iff v 1 _ (by rw [map_div₀, hx, div_one]; exact ha), map_one]
    have hu0 : 1 + π ^ e * b / x ≠ 0 := fun h ↦ by rw [h, map_zero] at hu1; exact zero_ne_one hu1
    have hsplit : Units.mk0 (x + π ^ e * b) hxa0 = Units.mk0 x hx0 * Units.mk0 _ hu0 :=
      Units.ext (by simp only [Units.val_mul, Units.val_mk0]; field_simp)
    rw [hsplit, map_mul, ratDirichletLocalChar_eq_one hχ v (Units.mk0 _ hu0) hu1 (by
      rw [Units.val_mk0, show 1 + π ^ e * b / x - 1 = π ^ e * (b / x) by ring,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hπ0), map_div₀, hx, div_one]
      exact hb1), mul_one]
  · rw [Set.indicator_of_notMem (fun h ↦ hx ((mem_unitsImage_iff v _).mp h)),
      Set.indicator_of_notMem (fun h ↦ hx ((valued_add_eq_one_iff v x _ ha).mp
        ((mem_unitsImage_iff v _).mp h)))]

/-- Paper: (11.3.1.3), p. 494, and `finiteStandardGaussian`, Ch03 Sec4, p. 152, at `q ∣ N`.
**Fourier support of the local factor.** For `q ∣ N` the factor `c_q⁻¹ · 1_{ℤ_q^×}` of the
Dirichlet test has Fourier transform vanishing outside `{|ξ|_q ≤ q^{e_q}}`, `e_q = v_q(N)`. -/
theorem unitCharTest_fourier_support (hχ : χ.IsPrimitive) (v : Vℚ) (hv : pr v ∣ N)
    (ξ : v.adicCompletion ℚ) (hξ : (pr v : ℝ) ^ N.factorization (pr v) < ‖ξ‖) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v) (unitCharTestFun v (ratDirichletLocalChar hχ v)) ξ = 0 :=
  ratLocalFourier_eq_zero_of_translate v _ _ (fun x b hb ↦ unitCharTestFun_translate hχ v hv x b hb)
    ξ hξ


/-! ### The exact conductor of the local component (primitivity) -/

private theorem unitPart_ofAdic (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) : unitPart (ι v u) = ι v u := by
  have h := ratPart_ofAdicCompletion v u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
  rw [zpow_zero] at h
  rw [unitPart_apply, h, map_one, inv_one, mul_one]

private theorem equivPi_apply_eq_cast (a : ZMod N) (p : N.primeFactors) :
    ZMod.equivPi N (NeZero.ne N) a p =
      ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p)) a := by
  have key : (Pi.evalRingHom (fun p : N.primeFactors ↦ ZMod ((p : ℕ) ^ N.factorization p)) p).comp
      (ZMod.equivPi N (NeZero.ne N)).toRingHom = ZMod.castHom (Nat.ordProj_dvd N p) _ :=
    Subsingleton.elim _ _
  exact congrArg (fun φ : ZMod N →+* _ ↦ φ a) key

/-- The residue `r(x) ∈ ℤ/N` of the idele `n` at `v = q` (with `n` the representative of a unit
`a` mod `N` that is `1` mod `N/q`) is `a`. -/
private theorem resMod_ofAdic_natCast (v : Vℚ) (hv : pr v ∣ N) (a : ZMod N)
    (ha : ZMod.castHom (Nat.div_dvd_of_dvd hv) (ZMod (N / pr v)) a = 1)
    (u : (v.adicCompletion ℚ)ˣ) (hu : (u : v.adicCompletion ℚ) = (a.val : v.adicCompletion ℚ))
    (hu1 : Valued.v (u : v.adicCompletion ℚ) = 1) :
    resMod N (ι v u) = a := by
  rw [resMod_apply, resModFun, unitPart_ofAdic v u hu1,
    (ZMod.equivPi N (NeZero.ne N)).symm_apply_eq]
  funext p
  rw [equivPi_apply_eq_cast]
  by_cases hpv : placeP N p = v
  · subst hpv
    rw [compV_ofAdicCompletion_self, hu, redP_natCast, ZMod.natCast_val, ZMod.castHom_apply]
  · rw [compV_ofAdicCompletion_ne hpv, Units.val_one, redP_one]
    have hpq : (p : ℕ) ≠ pr v := fun h ↦ hpv ((eq_placeOf_iff v p _).mpr h.symm).symm
    have hdvd : (p : ℕ) ^ N.factorization p ∣ N / pr v := by
      have hcop : Nat.Coprime ((p : ℕ) ^ N.factorization p) (pr v) :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
          (pr_prime v)).mpr hpq)
      exact hcop.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hv]; exact Nat.ordProj_dvd N p)
    have hcomp : ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p)) =
        (ZMod.castHom hdvd _).comp (ZMod.castHom (Nat.div_dvd_of_dvd hv) (ZMod (N / pr v))) :=
      Subsingleton.elim _ _
    rw [hcomp, RingHom.comp_apply, ha, map_one]

/-- Paper: (11.3.1.3), p. 494, local input; `DirichletCharacter.IsPrimitive`.
**The local component has conductor exactly `q^{e_q}`.** For `χ` primitive mod `N` and `q ∣ N`,
the local component `c_q` of `ψ` is not trivial on `1 + q^{e_q - 1} ℤ_q`. (It is trivial on
`1 + q^{e_q} ℤ_q` by `ratDirichletLocalChar_eq_one`.) Equivalently, the `q`-component of `χ` is
primitive mod `q^{e_q}`. -/
theorem exists_ratDirichletLocalChar_ne_one (hχ : χ.IsPrimitive) (v : Vℚ) (hv : pr v ∣ N) :
    ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧
      Valued.v (((u : v.adicCompletion ℚ) - 1) /
        (pr v : v.adicCompletion ℚ) ^ (N.factorization (pr v) - 1)) ≤ 1 ∧
      ratDirichletLocalChar hχ v u ≠ 1 := by
  by_contra! hall
  have hq := pr_prime v
  have hN0 : N ≠ 0 := NeZero.ne N
  have hd : N / pr v ∣ N := Nat.div_dvd_of_dvd hv
  have he : 1 ≤ N.factorization (pr v) := hq.factorization_pos_of_dvd hN0 hv
  have hpow : pr v ^ (N.factorization (pr v) - 1) ∣ N / pr v := by
    refine Nat.dvd_of_mul_dvd_mul_right hq.pos ?_
    rw [← pow_succ, Nat.sub_add_cancel he, Nat.div_mul_cancel hv]
    exact Nat.ordProj_dvd N (pr v)
  have hft : χ.FactorsThrough (N / pr v) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr fun a ha ↦ ?_
    have ha' : ZMod.castHom hd (ZMod (N / pr v)) (a : ZMod N) = 1 := by
      have h := congrArg Units.val (MonoidHom.mem_ker.mp ha)
      simpa [ZMod.unitsMap_def] using h
    set n := (a : ZMod N).val with hn
    have hcop : Nat.gcd n N = 1 := ZMod.val_coe_unit_coprime a
    have hqn : ¬ ((pr v : ℕ) : ℤ) ∣ (n : ℤ) := by
      intro h
      have h1 := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp h) hv
      rw [hcop] at h1
      exact hq.not_dvd_one h1
    have hval : Valued.v ((n : v.adicCompletion ℚ)) = 1 := by
      have h := (ratBridge_valued_intCast_eq_one_iff v n).mpr hqn
      simpa using h
    have hn0 : (n : v.adicCompletion ℚ) ≠ 0 := fun h ↦ by
      rw [h, map_zero] at hval; exact zero_ne_one hval
    let u := Units.mk0 _ hn0
    set M := pr v ^ (N.factorization (pr v) - 1)
    have hM : ((1 : ℤ) : ZMod M) = ((n : ℤ) : ZMod M) := by
      have h := congrArg (ZMod.castHom hpow (ZMod M)) ha'
      rw [map_one, ← RingHom.comp_apply,
        (Subsingleton.elim _ _ : (ZMod.castHom hpow (ZMod M)).comp (ZMod.castHom hd _) =
          ZMod.castHom (hpow.trans hd) (ZMod M)), ZMod.castHom_apply, ← ZMod.natCast_val] at h
      rw [Int.cast_one, Int.cast_natCast, hn, h]
    obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 n M).mp hM
    have hq0 : (pr v : v.adicCompletion ℚ) ≠ 0 := (ratPrime_isUniformizer v).ne_zero
    have hcong : Valued.v (((u : v.adicCompletion ℚ) - 1) /
        (pr v : v.adicCompletion ℚ) ^ (N.factorization (pr v) - 1)) ≤ 1 := by
      have e1 : (u : v.adicCompletion ℚ) - 1 =
          (pr v : v.adicCompletion ℚ) ^ (N.factorization (pr v) - 1) *
            (m : v.adicCompletion ℚ) := by
        have h := congrArg (fun z : ℤ ↦ (z : v.adicCompletion ℚ)) hm
        simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_mul, Int.cast_pow,
          M, Nat.cast_pow] at h
        rw [Units.val_mk0, h]
      rw [e1, mul_div_cancel_left₀ _ (pow_ne_zero _ hq0)]
      have h := ratBridge_valued_intCast_le_one v m
      simpa using h
    have hc := hall u hval hcong
    rw [ratDirichletLocalChar_apply, coe_ideleChar] at hc
    have hr : (resMod N).toHomUnits (ι v u) = a :=
      Units.ext (by
        rw [MonoidHom.coe_toHomUnits]
        exact resMod_ofAdic_natCast v hv a ha' u rfl hval)
    rw [hr, inv_eq_one] at hc
    exact MonoidHom.mem_ker.mpr (Units.ext hc)
  have hle : χ.conductor ≤ N / pr v :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
  rw [show χ.conductor = N from hχ] at hle
  exact absurd hle (not_le.mpr (Nat.div_lt_self (Nat.pos_of_ne_zero hN0) hq.one_lt))


/-- The integral of `c_q⁻¹ · 1_{ℤ_q^×}` vanishes for `q ∣ N`, since `c_q` is not trivial on the
units. -/
theorem integral_unitCharTestFun (hχ : χ.IsPrimitive) (v : Vℚ) (hv : pr v ∣ N) :
    ∫ x, unitCharTestFun v (ratDirichletLocalChar hχ v) x ∂ν𝔭(v) = 0 := by
  obtain ⟨u, hu1, -, hne⟩ := exists_ratDirichletLocalChar_ne_one hχ v hv
  have hnorm : ‖(u : v.adicCompletion ℚ)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr hu1
  set c := ratDirichletLocalChar hχ v
  have hpt (y : v.adicCompletion ℚ) :
      unitCharTestFun v c (u * y) = (c u)⁻¹ * unitCharTestFun v c y := by
    unfold unitCharTestFun
    by_cases hy : Valued.v y = 1
    · have huy : Valued.v ((u : v.adicCompletion ℚ) * y) = 1 := by rw [map_mul, hu1, hy, one_mul]
      have hy0 : y ≠ 0 := fun h ↦ by rw [h, map_zero] at hy; exact zero_ne_one hy
      have huy0 : (u : v.adicCompletion ℚ) * y ≠ 0 := mul_ne_zero u.ne_zero hy0
      rw [Set.indicator_of_mem ((mem_unitsImage_iff v _).mpr huy),
        Set.indicator_of_mem ((mem_unitsImage_iff v _).mpr hy)]
      simp only [ne_eq, hy0, huy0, not_false_eq_true, ↓reduceDIte]
      rw [show Units.mk0 ((u : v.adicCompletion ℚ) * y) huy0 = u * Units.mk0 y hy0 from
        Units.ext rfl, map_mul, mul_inv]
    · have huy : Valued.v ((u : v.adicCompletion ℚ) * y) ≠ 1 := by rwa [map_mul, hu1, one_mul]
      rw [Set.indicator_of_notMem (fun h ↦ huy ((mem_unitsImage_iff v _).mp h)),
        Set.indicator_of_notMem (fun h ↦ hy ((mem_unitsImage_iff v _).mp h)), mul_zero]
  have h := ratLocal_integral_comp_mul v u hnorm (unitCharTestFun v c)
  simp_rw [hpt] at h
  rw [integral_const_mul] at h
  by_contra hI
  exact hne (inv_eq_one.mp ((mul_eq_right₀ hI).mp h))

end LocalSupport

/-! ### The Dirichlet test in the absolute Paley–Wiener level -/

section PW

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

local notation "Sχ" => ratDirichletS N

private theorem unitCharTestFun_zero (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) :
    unitCharTestFun v c 0 = 0 := by
  unfold unitCharTestFun
  exact Set.indicator_of_notMem (fun h ↦ by
    rw [mem_unitsImage_iff, map_zero] at h; exact zero_ne_one h) _

private theorem exists_mem_ratDirichletS (hN : 1 < N) : ∃ v : Vℚ, v ∈ Sχ := by
  have hp := Nat.minFac_prime (show N ≠ 1 by omega)
  refine ⟨placeOf _ hp, (mem_ratDirichletS (NeZero.ne N) _).mpr ?_⟩
  rw [pr_placeOf]
  exact Nat.minFac_dvd N

private theorem localFourier_zero (v : Vℚ) (F : v.adicCompletion ℚ → ℂ) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v) F 0 = ∫ x, F x ∂ν𝔭(v) := by
  unfold tamagawaFourier
  simp only [mul_zero, finiteLocalStandardCharacter_zero, Circle.coe_one, star_one, mul_one]

/-- The S-local Fourier transform of the S-local Dirichlet test: the real Fourier transform of `f`
at the archimedean coordinate times the local Fourier transforms of `c_q⁻¹ · 1_{ℤ_q^×}`. -/
theorem dirSLocalTest_fourier (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) (y : SAdeleRing ℚ Sχ) :
    sAdeleSchwartzFourier (dirSLocalTest hχ f) (Multiplicative.ofAdd y) =
      𝓕 f (realCoord (y.1 Rat.infinitePlace)) *
        ∏ w : Sχ, tamagawaFourier ν𝔭(w.val) ψ𝔭(w.val)
          (unitCharTestFun w.val (ratDirichletLocalChar hχ w.val)) (y.2 w) := by
  rw [ratSLocalFourier_prod Sχ _ (fun z ↦ f (realCoord (z Rat.infinitePlace)))
    (fun w ↦ unitCharTestFun w.val (ratDirichletLocalChar hχ w.val)) (dirSLocalTest_apply hχ f) y,
    ratArchFourier_archTest]

/-- Paper: Definition 2.2.4.4, p. 91, for the Dirichlet test.
**The Dirichlet test is polar**: it vanishes at `0` (its factor at `q ∣ N` does) and its Fourier
transform vanishes at `0` (the integral of `c_q⁻¹ · 1_{ℤ_q^×}` does, `c_q` being ramified). -/
theorem dirTest_mem_polarSubspace (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ)) :
    dirTest hχ f ∈ adelePolarSubspace ℚ := by
  obtain ⟨v₀, hv₀⟩ := exists_mem_ratDirichletS (N := N) hN
  have hdv : pr v₀ ∣ N := (mem_ratDirichletS (NeZero.ne N) v₀).mp hv₀
  rw [dirTest, sAdeleSchwartzToGlobal_mem_polarSubspace_iff]
  constructor
  · rw [dirSLocalTest_apply]
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_univ ⟨v₀, hv₀⟩) (unitCharTestFun_zero _ _))
  · rw [dirSLocalTest_fourier]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨v₀, hv₀⟩) ?_)
    rw [show (0 : SAdeleRing ℚ Sχ).2 ⟨v₀, hv₀⟩ = 0 from rfl, localFourier_zero,
      integral_unitCharTestFun hχ v₀ hdv]

private theorem transition_refl (S : Finset Vℚ)
    (k : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    sAdeleSchwartzTransition ℚ (le_rfl : S ⊆ S) k = k := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : SAdeleRing ℚ S, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [sAdeleSchwartzTransition_apply, ite_eq_left_of_eq_true _ _ (eq_true fun w hw ↦ absurd w.2 hw)]

/-- Paper: (11.3.1.3), p. 494, and Definition 7.3.2.1(1), p. 351, over `ℚ`.
**The Dirichlet test is in the absolute Paley–Wiener level.** If the real test `f` has Fourier
support in `[-X, X]` and `X ≥ q^{e_q}` for every `q ∣ N`, then `dirTest χ f` (polar by
`dirTest_mem_polarSubspace`) lies in `primaryDivisorialAbsolutePWTests ℚ S X`, `S` the places
over the primes dividing `N`. -/
theorem dirTest_mem_absolutePWTests (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ)) {X : ℝ}
    (hf : tsupport (fun x : ℝ ↦ (𝓕 f) x) ⊆ Set.Icc (-X) X)
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    (⟨dirTest hχ f, dirTest_mem_polarSubspace hχ hN f⟩ : adelePolarSubspace ℚ) ∈
      primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X := by
  change dirTest hχ f ∈ (sLocalPWTests le_rfl (sLocalPWBox Sχ X)).map (sAdeleSchwartzToGlobal ℚ Sχ)
  refine ⟨dirSLocalTest hχ f, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_sLocalPWTests]
  refine ⟨dirSLocalTest hχ f, transition_refl _ _, ?_⟩
  set K : Set (Multiplicative (SAdeleRing ℚ Sχ)) := Multiplicative.toAdd ⁻¹' sLocalPWBox Sχ X
  have hKc : IsCompact K := by
    have hK : K = Multiplicative.ofAdd '' sLocalPWBox Sχ X := by
      ext y
      exact ⟨fun h ↦ ⟨y.toAdd, h, rfl⟩, fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz⟩
    rw [hK]
    exact (isCompact_sLocalPWBox (S := Sχ) X).image continuous_ofAdd
  have hsupp : Function.support (sAdeleSchwartzFourier (dirSLocalTest hχ f)).val ⊆ K := by
    intro y hy
    obtain ⟨y, rfl⟩ : ∃ z, Multiplicative.ofAdd z = y := ⟨y.toAdd, rfl⟩
    have hy' : sAdeleSchwartzFourier (dirSLocalTest hχ f) (Multiplicative.ofAdd y) ≠ 0 := hy
    rw [dirSLocalTest_fourier] at hy'
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hy'
    refine ⟨fun w ↦ ?_, fun w ↦ ?_⟩
    · obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      have hr := hf (subset_tsupport _ h1)
      have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) (y.1 Rat.infinitePlace)
      change ‖realCoord (y.1 Rat.infinitePlace)‖ = _ at hn
      have hm : Rat.infinitePlace.mult = 1 := by
        simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
      change ‖y.1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult ≤ X
      rw [hm, pow_one, ← hn, Real.norm_eq_abs]
      exact abs_le.mpr hr
    · have hw := Finset.prod_ne_zero_iff.mp h2 w (Finset.mem_univ _)
      have hdv : pr w.val ∣ N := (mem_ratDirichletS (NeZero.ne N) _).mp w.2
      by_contra hlt
      exact hw (unitCharTest_fourier_support hχ w.val hdv (y.2 w)
        (lt_of_le_of_lt (hX _ (Nat.mem_primeFactors.mpr ⟨pr_prime _, hdv, NeZero.ne N⟩))
          (not_le.mp hlt)))
  let : T2Space (Multiplicative (SAdeleRing ℚ Sχ)) :=
    inferInstanceAs (T2Space (((w : InfinitePlace ℚ) → w.Completion) ×
      ((v : Sχ) → v.val.adicCompletion ℚ)))
  have hcl : tsupport (sAdeleSchwartzFourier (dirSLocalTest hχ f)).val ⊆ K :=
    closure_minimal hsupp hKc.isClosed
  exact ⟨hKc.of_isClosed_subset (isClosed_tsupport _) hcl, hcl⟩

end PW

end RiemannMasullo.Isolated
