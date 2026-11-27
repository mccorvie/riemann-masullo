module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_Locala_Isolated
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# Local theory at the primes of the conductor: exact support and the box decomposition

Workstream B for #7351, stage 3b (items 5–6 of stage 3).

* `ratLocalFourier_inversion`, `ratLocalFourier_ne_zero`: Fourier inversion on `ℚ_q` for the
  Tamagawa measure and the standard character, from `sLocal_fourier_inversion` at `S = {q}`; a
  nonzero test has a nonzero Fourier transform.
* `shellTestFun_fourier_ne_zero_iff` (item 5): the Fourier transform of the twisted shell
  `c_q(x/q^a)⁻¹ · 1_{|x| = q^{-a}}` is supported exactly on `|ξ| = q^{e_q + a}`.
* `sLocalPW_eq_finset_sum_pure` (item 6): an S-local test whose Fourier transform is supported in
  the box `sLocalPWBox S X` is a finite sum of pure tensors whose archimedean factors are real
  tests with Fourier support in `[-X, X]` and whose local factors have Fourier support in
  `{|ξ| ≤ X}`. The decomposition is made on the Fourier side.

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal ENNReal SchwartzMap FourierTransform NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

open NumberFieldKB.Chebotarev.RatIdele

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "realCoord" =>
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "ν𝔭(" v ")" => finiteLocalAdditiveTamagawaMeasure ℚ v
local notation "ψ𝔭(" v ")" => finiteLocalStandardCharacter ℚ v
local notation "SB(" v ")" => SchwartzBruhat (Multiplicative (HeightOneSpectrum.adicCompletion ℚ v))
local notation "F𝔭(" v ")" => tamagawaFourier ν𝔭(v) ψ𝔭(v)

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

/-! ### Local Fourier transform and inversion on `ℚ_q` -/

section LocalInversion

/-- The local Fourier transform of a Schwartz–Bruhat test on `ℚ_q` is Schwartz–Bruhat. -/
theorem ratLocalFourier_mem (v : Vℚ) (f : SB(v)) :
    (fun y : Multiplicative (v.adicCompletion ℚ) ↦
      F𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd) ∈
        schwartzBruhatSubmodule (Multiplicative (v.adicCompletion ℚ)) := by
  let G := Multiplicative (v.adicCompletion ℚ)
  let μ : Measure G := ν𝔭(v)
  let : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  let : T2Space G := inferInstanceAs (T2Space (v.adicCompletion ℚ))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace (v.adicCompletion ℚ))
  let : BorelSpace G := inferInstanceAs (BorelSpace (v.adicCompletion ℚ))
  have hadd : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hadd.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hadd.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hadd.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular ℚ v
  obtain ⟨e, he, -⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual ℚ v
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  let g : schwartzBruhatSubmodule (PontryaginDual G) := fourier f
  have hEq (y : G) : F𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd = g.val (e y) := by
    rw [tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ by
      rw [mul_comm x y.toAdd]
      exact he y.toAdd x)]
    exact ((hfourier f).2 (e y)).symm
  rw [funext hEq]
  exact schwartzBruhat_mem_comp_equiv e g.property

/-- The local Fourier transform on `ℚ_q` as a Schwartz–Bruhat test. -/
def ratLocalFourierSB (v : Vℚ) (f : SB(v)) : SB(v) :=
  ⟨_, ratLocalFourier_mem v f⟩

theorem ratLocalFourierSB_apply (v : Vℚ) (f : SB(v)) (y : v.adicCompletion ℚ) :
    ratLocalFourierSB v f (Multiplicative.ofAdd y) =
      F𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x)) y := rfl

private theorem schwartz_fourier_fourier_zero (φ : 𝓢(ℝ, ℂ)) : 𝓕 (𝓕 φ) 0 = φ 0 := by
  have h : φ 0 = (𝓕⁻ (𝓕 φ)) 0 := by rw [FourierTransform.fourierInv_fourier_eq]
  rw [h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero,
    SchwartzMap.fourier_coe]

/-- Paper: §A.3.1.1, p. 557, at a finite place of `ℚ`.
**Local Fourier inversion.** For the Tamagawa measure and the standard character of `ℚ_q`, the
Fourier transform applied twice is the reflection. Derived from `sLocal_fourier_inversion` at
`S = {q}` on the product of a Gaussian at infinity with the test. -/
theorem ratLocalFourier_inversion (v : Vℚ) (f : SB(v)) (t : v.adicCompletion ℚ) :
    F𝔭(v) (F𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x))) t = f (Multiplicative.ofAdd (-t)) := by
  classical
  let S : Finset Vℚ := {v}
  let i : S := ⟨v, Finset.mem_singleton_self v⟩
  have hi : ∀ j : S, j = i := fun j ↦ Subtype.ext (Finset.mem_singleton.mp j.2)
  let φ : 𝓢(ℝ, ℂ) := (SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM
  have hφ0 : φ 0 = 1 := by
    simp [φ, SchwartzMap.postcompCLM_apply, SchwartzMap.gaussian_apply]
  let fam : ∀ j : S, SB(j.val) := Pi.single i f
  let k := (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose
    (archTest φ ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, fam j))
  let b : (j : S) → j.val.adicCompletion ℚ → ℂ := fun j x ↦ fam j (Multiplicative.ofAdd x)
  have hb : b i = fun x ↦ f (Multiplicative.ofAdd x) := funext fun x ↦ by simp [b, fam]
  have hk (x : SAdeleRing ℚ S) : k (Multiplicative.ofAdd x) =
      φ (realCoord (x.1 Rat.infinitePlace)) * ∏ j, b j (x.2 j) := by
    rw [(sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose_spec, archTest_apply]
  have h1 (y : SAdeleRing ℚ S) : sAdeleSchwartzFourier k (Multiplicative.ofAdd y) =
      𝓕 φ (realCoord (y.1 Rat.infinitePlace)) * ∏ j, F𝔭(j.val) (b j) (y.2 j) := by
    rw [ratSLocalFourier_prod S k (fun z ↦ φ (realCoord (z Rat.infinitePlace))) b hk y,
      ratArchFourier_archTest]
  have h2 (y : SAdeleRing ℚ S) :
      sAdeleSchwartzFourier (sAdeleSchwartzFourier k) (Multiplicative.ofAdd y) =
        𝓕 (𝓕 φ) (realCoord (y.1 Rat.infinitePlace)) *
          ∏ j, F𝔭(j.val) (F𝔭(j.val) (b j)) (y.2 j) := by
    rw [ratSLocalFourier_prod S (sAdeleSchwartzFourier k)
      (fun z ↦ 𝓕 φ (realCoord (z Rat.infinitePlace))) (fun j ↦ F𝔭(j.val) (b j)) h1 y,
      ratArchFourier_archTest]
  let y₀ : SAdeleRing ℚ S := (0, Pi.single i t)
  have hinv := sLocal_fourier_inversion k y₀
  rw [h2, hk] at hinv
  rw [Fintype.prod_eq_single i (fun j hj ↦ absurd (hi j) hj),
    Fintype.prod_eq_single i (fun j hj ↦ absurd (hi j) hj), hb] at hinv
  have e1 : y₀.2 i = t := Pi.single_eq_same _ _
  have e2 : (-y₀).2 i = -t := by
    change -(y₀.2 i) = -t
    rw [e1]
  have e3 : realCoord (y₀.1 Rat.infinitePlace) = 0 := map_zero _
  have e4 : realCoord ((-y₀).1 Rat.infinitePlace) = 0 := by
    change realCoord (-(y₀.1 Rat.infinitePlace)) = 0
    rw [map_neg, e3, neg_zero]
  dsimp only at hinv
  rw [e1, e2, e3, e4, schwartz_fourier_fourier_zero, hφ0, one_mul, one_mul] at hinv
  exact hinv

/-- **Local Fourier injectivity.** A nonzero test on `ℚ_q` has a nonzero Fourier transform. -/
theorem ratLocalFourier_ne_zero (v : Vℚ) (f : SB(v))
    (hf : ∃ x, f (Multiplicative.ofAdd x) ≠ 0) :
    ∃ ξ, F𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x)) ξ ≠ 0 := by
  by_contra! h
  obtain ⟨x, hx⟩ := hf
  have hi := ratLocalFourier_inversion v f (-x)
  rw [neg_neg] at hi
  apply hx
  rw [← hi, show F𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x)) = fun _ ↦ 0 from funext h]
  unfold tamagawaFourier
  simp only [zero_mul, integral_zero]

end LocalInversion


/-! ### Item 5: exact Fourier support of the twisted shells -/

section Shell

private theorem integral_comp_mul_unit (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ)
    (h : v.adicCompletion ℚ → ℂ) :
    (∫ y, h (u.val * y) ∂ν𝔭(v)) = (‖u.val‖⁻¹ : ℝ) • ∫ z, h z ∂ν𝔭(v) := by
  let : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  let e := (Homeomorph.mulLeft₀ u.val u.ne_zero).toMeasurableEquiv
  calc (∫ y, h (u.val * y) ∂ν𝔭(v)) = ∫ y, h (e y) ∂ν𝔭(v) := rfl
    _ = ∫ z, h z ∂((ν𝔭(v)).map e) := (integral_map_equiv e h).symm
    _ = _ := by
      rw [show ⇑e = (u.val * · : _ → _) from rfl, ratLocal_map_mul, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _))]

private theorem mem_unitsImage_iff' (v : Vℚ) (y : v.adicCompletion ℚ) :
    y ∈ Units.val '' ((v.adicCompletionIntegers ℚ).units : Set (v.adicCompletion ℚ)ˣ) ↔
      Valued.v y = 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hw
  · intro hy
    have hy0 : y ≠ 0 := fun h ↦ by rw [h, map_zero] at hy; exact zero_ne_one hy
    exact ⟨Units.mk0 y hy0,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hy, rfl⟩

private theorem valued_pr' (v : Vℚ) :
    Valued.v (pr v : v.adicCompletion ℚ) = WithZero.exp (-1) := by
  simpa only [Rat.cast_natCast, eq_self, ↓reduceIte] using valued_prime v (pr_prime v)

private theorem ratLocalChar_add' (v : Vℚ) (x y : v.adicCompletion ℚ) :
    ψ𝔭(v) (x + y) = ψ𝔭(v) x * ψ𝔭(v) y := by
  obtain ⟨ψ, hψ, -⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom ℚ v
  rw [← hψ, ← hψ, ← hψ, ofAdd_add, map_mul]

/-- The standard character of `ℚ_p` is trivial on `ℤ_p`. -/
private theorem ratLocalChar_eq_one_of_norm_le (v : Vℚ) (x : v.adicCompletion ℚ) (hx : ‖x‖ ≤ 1) :
    ψ𝔭(v) x = 1 := by
  have h1 : (1 : v.adicCompletion ℚ) ∈ {y : v.adicCompletion ℚ | ‖y‖ ≤
      (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 ℚ))} := by
    simp only [Set.mem_ofPred_eq, norm_one]
    exact one_le_pow₀ (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le)
  rw [← finiteLocalStandardCharacter_annihilator_integers] at h1
  have := h1 x (Valued.toNormedField.norm_le_one_iff.mp hx)
  rwa [mul_one] at this

/-- Norms on `ℚ_p` are integer powers of `p`. -/
private theorem ratNorm_eq_zpow (v : Vℚ) {η : v.adicCompletion ℚ} (hη : η ≠ 0) :
    ∃ m : ℤ, ‖η‖ = (pr v : ℝ) ^ m := by
  have hv0 : Valued.v η ≠ 0 := (Valuation.ne_zero_iff _).mpr hη
  set k := WithZero.log (Valued.v η)
  let π := ratPrimeUnit v
  have hp0 : (0 : ℝ) < pr v := by exact_mod_cast (pr_prime v).pos
  have h1 : Valued.v (η * ((π ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = 1 := by
    rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, ratPrimeUnit_val, valued_pr',
      ← WithZero.exp_log hv0, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
    rw [show k + k * -1 = 0 by ring, WithZero.exp_zero]
  have hn := Valued.toNormedField.norm_eq_one_iff.mpr h1
  rw [norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, ratPrimeUnit_val, ratPrime_norm,
    inv_zpow, mul_inv_eq_one₀ (zpow_ne_zero _ hp0.ne')] at hn
  exact ⟨k, hn⟩

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private theorem unitCharTestFun_mul (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ)
    (u : (v.adicCompletion ℚ)ˣ) (hu1 : Valued.v (u : v.adicCompletion ℚ) = 1)
    (y : v.adicCompletion ℚ) :
    unitCharTestFun v c (u * y) = (c u)⁻¹ * unitCharTestFun v c y := by
  unfold unitCharTestFun
  by_cases hy : Valued.v y = 1
  · have huy : Valued.v ((u : v.adicCompletion ℚ) * y) = 1 := by rw [map_mul, hu1, hy, one_mul]
    have hy0 : y ≠ 0 := fun h ↦ by rw [h, map_zero] at hy; exact zero_ne_one hy
    have huy0 : (u : v.adicCompletion ℚ) * y ≠ 0 := mul_ne_zero u.ne_zero hy0
    rw [Set.indicator_of_mem ((mem_unitsImage_iff' v _).mpr huy),
      Set.indicator_of_mem ((mem_unitsImage_iff' v _).mpr hy)]
    simp only [ne_eq, hy0, huy0, not_false_eq_true, ↓reduceDIte]
    rw [show Units.mk0 ((u : v.adicCompletion ℚ) * y) huy0 = u * Units.mk0 y hy0 from
      Units.ext rfl, map_mul, mul_inv]
  · have huy : Valued.v ((u : v.adicCompletion ℚ) * y) ≠ 1 := by rwa [map_mul, hu1, one_mul]
    rw [Set.indicator_of_notMem (fun h ↦ huy ((mem_unitsImage_iff' v _).mp h)),
      Set.indicator_of_notMem (fun h ↦ hy ((mem_unitsImage_iff' v _).mp h)), mul_zero]

private theorem unitCharTestFun_ne_zero_valued (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ)
    {y : v.adicCompletion ℚ} (hy : unitCharTestFun v c y ≠ 0) : Valued.v y = 1 := by
  by_contra h
  apply hy
  unfold unitCharTestFun
  exact Set.indicator_of_notMem (fun h' ↦ h ((mem_unitsImage_iff' v _).mp h')) _

/-- Rotating the frequency by a unit multiplies the Fourier transform of `c⁻¹ 1_{ℤ_q^×}` by a
nonzero factor. -/
private theorem unitCharTest_fourier_rotate (hχ : χ.IsPrimitive) (v : Vℚ)
    (w : (v.adicCompletion ℚ)ˣ) (hw : Valued.v (w : v.adicCompletion ℚ) = 1)
    (ξ : v.adicCompletion ℚ) :
    F𝔭(v) (unitCharTestFun v (ratDirichletLocalChar hχ v)) (w * ξ) =
      (ratDirichletLocalChar hχ v w⁻¹)⁻¹ *
        F𝔭(v) (unitCharTestFun v (ratDirichletLocalChar hχ v)) ξ := by
  set c := ratDirichletLocalChar hχ v
  have hwn : ‖(w : v.adicCompletion ℚ)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr hw
  have hwi : Valued.v ((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hw, inv_one]
  unfold tamagawaFourier
  have h := ratLocal_integral_comp_mul v w hwn
    (fun z ↦ unitCharTestFun v c ((w⁻¹ : (v.adicCompletion ℚ)ˣ) * z) * star (ψ𝔭(v) (z * ξ) : ℂ))
  rw [← integral_const_mul]
  refine Eq.trans ?_ (h.trans (integral_congr_ae (.of_forall fun z ↦ ?_)))
  · refine integral_congr_ae (.of_forall fun y ↦ ?_)
    have e1 : ((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
        ((w : v.adicCompletion ℚ) * y) = y := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    simp only
    rw [e1, show (w : v.adicCompletion ℚ) * y * ξ = y * (w * ξ) by ring]
  · simp only
    rw [unitCharTestFun_mul v c _ hwi, mul_assoc]

/-- **The Fourier transform of `c_q⁻¹ · 1_{ℤ_q^×}` is supported exactly on `|ξ| = q^{e_q}`.** -/
theorem unitCharTest_fourier_ne_zero_iff (hχ : χ.IsPrimitive) (v : Vℚ) (hv : pr v ∣ N)
    (η : v.adicCompletion ℚ) :
    F𝔭(v) (unitCharTestFun v (ratDirichletLocalChar hχ v)) η ≠ 0 ↔
      ‖η‖ = (pr v : ℝ) ^ N.factorization (pr v) := by
  set c := ratDirichletLocalChar hχ v
  set e := N.factorization (pr v)
  have he : 1 ≤ e := (pr_prime v).factorization_pos_of_dvd (NeZero.ne N) hv
  have hp1 : (1 : ℝ) < pr v := by exact_mod_cast (pr_prime v).one_lt
  have hp0 : (0 : ℝ) < pr v := by linarith
  -- small frequencies
  have hsmall (ξ : v.adicCompletion ℚ) (hξ : ‖ξ‖ < (pr v : ℝ) ^ e) :
      F𝔭(v) (unitCharTestFun v c) ξ = 0 := by
    have hξ' : ‖ξ‖ ≤ (pr v : ℝ) ^ (e - 1) := by
      by_cases h0 : ξ = 0
      · rw [h0, norm_zero]; positivity
      obtain ⟨m, hm⟩ := ratNorm_eq_zpow v h0
      rw [hm] at hξ ⊢
      rw [← zpow_natCast] at hξ ⊢
      have := (zpow_lt_zpow_iff_right₀ hp1).mp hξ
      exact zpow_le_zpow_right₀ hp1.le (by push_cast [Nat.cast_sub he]; omega)
    obtain ⟨u, hu1, hcong, hne⟩ := exists_ratDirichletLocalChar_ne_one hχ v hv
    have hun : ‖(u : v.adicCompletion ℚ)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr hu1
    have hpe : ‖(pr v : v.adicCompletion ℚ) ^ (e - 1)‖ = ((pr v : ℝ) ^ (e - 1))⁻¹ := by
      rw [norm_pow, ratPrime_norm, inv_pow]
    have hu1' : ‖(u : v.adicCompletion ℚ) - 1‖ ≤ ((pr v : ℝ) ^ (e - 1))⁻¹ := by
      have h := Valued.toNormedField.norm_le_one_iff.mpr hcong
      rw [norm_div, hpe, div_le_one (by positivity)] at h
      exact h
    have hshift : F𝔭(v) (unitCharTestFun v c) ξ = (c u)⁻¹ * F𝔭(v) (unitCharTestFun v c) ξ := by
      unfold tamagawaFourier
      rw [← integral_const_mul,
        ← ratLocal_integral_comp_mul v u hun
          (fun y ↦ unitCharTestFun v c y * star (ψ𝔭(v) (y * ξ) : ℂ))]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      simp only
      rw [unitCharTestFun_mul v c u hu1]
      by_cases hy : unitCharTestFun v c y = 0
      · rw [hy, mul_zero, zero_mul, zero_mul, mul_zero]
      have hyv := unitCharTestFun_ne_zero_valued v c hy
      have hyn : ‖y‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr hyv
      have hint : ‖((u : v.adicCompletion ℚ) - 1) * y * ξ‖ ≤ 1 := by
        rw [norm_mul, norm_mul, hyn, mul_one]
        calc ‖(u : v.adicCompletion ℚ) - 1‖ * ‖ξ‖
            ≤ ((pr v : ℝ) ^ (e - 1))⁻¹ * (pr v : ℝ) ^ (e - 1) :=
              mul_le_mul hu1' hξ' (norm_nonneg _) (by positivity)
          _ = 1 := inv_mul_cancel₀ (by positivity)
      rw [show (u : v.adicCompletion ℚ) * y * ξ = y * ξ + ((u : v.adicCompletion ℚ) - 1) * y * ξ
        by ring, ratLocalChar_add', ratLocalChar_eq_one_of_norm_le v _ hint, mul_one]
      ring
    by_contra hF
    have h1 : (c u)⁻¹ = 1 := (mul_eq_right₀ hF).mp hshift.symm
    exact hne (inv_eq_one.mp h1)
  -- large frequencies
  have hlarge (ξ : v.adicCompletion ℚ) (hξ : (pr v : ℝ) ^ e < ‖ξ‖) :
      F𝔭(v) (unitCharTestFun v c) ξ = 0 := unitCharTest_fourier_support hχ v hv ξ hξ
  have hsupp (ξ : v.adicCompletion ℚ) (hξ : F𝔭(v) (unitCharTestFun v c) ξ ≠ 0) :
      ‖ξ‖ = (pr v : ℝ) ^ e := by
    rcases lt_trichotomy ‖ξ‖ ((pr v : ℝ) ^ e) with h | h | h
    · exact absurd (hsmall ξ h) hξ
    · exact h
    · exact absurd (hlarge ξ h) hξ
  refine ⟨hsupp η, fun hη ↦ ?_⟩
  -- the transform is not identically zero
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, F𝔭(v) (unitCharTestFun v c) η₀ ≠ 0 := by
    have h := ratLocalFourier_ne_zero v (unitCharTest v c) ⟨1, by
      rw [unitCharTest_apply]
      unfold unitCharTestFun
      rw [Set.indicator_of_mem ((mem_unitsImage_iff' v 1).mpr (map_one _))]
      simp⟩
    simpa only [unitCharTest_apply] using h
  have hn₀ := hsupp η₀ hη₀
  have hη₀0 : η₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hn₀; exact (pow_pos hp0 e).ne' hn₀.symm
  have hw0 : η / η₀ ≠ 0 := div_ne_zero (fun h ↦ by
    rw [h, norm_zero] at hη; exact (pow_pos hp0 e).ne' hη.symm) hη₀0
  let w := Units.mk0 (η / η₀) hw0
  have hwn : ‖(w : v.adicCompletion ℚ)‖ = 1 := by
    rw [Units.val_mk0, norm_div, hη, hn₀, div_self (pow_pos hp0 e).ne']
  have hw : Valued.v (w : v.adicCompletion ℚ) = 1 := Valued.toNormedField.norm_eq_one_iff.mp hwn
  have hηw : η = w * η₀ := by rw [Units.val_mk0, div_mul_cancel₀ _ hη₀0]
  rw [hηw, unitCharTest_fourier_rotate hχ v w hw]
  refine mul_ne_zero (inv_ne_zero ?_) hη₀
  rw [ratDirichletLocalChar_apply]
  exact Units.ne_zero _

/-- The twisted shell `x ↦ c(x / q^a)⁻¹ · 1_{|x| = q^{-a}}`, as `c⁻¹ 1_{ℤ_q^×}` at `x / q^a`. -/
def shellTestFun (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (a : ℤ)
    (x : v.adicCompletion ℚ) : ℂ :=
  unitCharTestFun v c ((((ratPrimeUnit v) ^ a)⁻¹ : (v.adicCompletion ℚ)ˣ) * x)

theorem shellTestFun_zero (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) :
    shellTestFun v c 0 = unitCharTestFun v c := by
  funext x
  simp [shellTestFun]

/-- The twisted shell is locally constant with compact support. -/
theorem shellTestFun_lc (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (a : ℤ) :
    IsLocallyConstant (shellTestFun v c a) ∧ HasCompactSupport (shellTestFun v c a) := by
  let u := ((ratPrimeUnit v) ^ a)⁻¹
  let h := Homeomorph.mulLeft₀ (u : v.adicCompletion ℚ) u.ne_zero
  have hc : shellTestFun v c a = unitCharTestFun v c ∘ h := rfl
  obtain ⟨hl, hcs⟩ := unitCharTestFun_lc v c
  rw [hc]
  exact ⟨hl.comp_continuous h.continuous, hcs.comp_homeomorph h⟩

/-- Paper: (11.3.1.3), p. 494, local input at `q ∣ N` (Gauss sums).
**Item 5: exact Fourier support of the twisted shells.** For `q ∣ N` and `a ∈ ℤ`, the Fourier
transform of the shell `c_q(x / q^a)⁻¹ · 1_{|x| = q^{-a}}` is nonzero exactly on
`|ξ| = q^{e_q + a}`, `e_q = v_q(N)`. Uses primitivity of `χ`.
Deviation: The shell is defined as `c_q⁻¹ 1_{ℤ_q^×}` evaluated at `x / q^a`. -/
theorem shellTestFun_fourier_ne_zero_iff (hχ : χ.IsPrimitive) (v : Vℚ) (hv : pr v ∣ N) (a : ℤ)
    (ξ : v.adicCompletion ℚ) :
    F𝔭(v) (shellTestFun v (ratDirichletLocalChar hχ v) a) ξ ≠ 0 ↔
      ‖ξ‖ = (pr v : ℝ) ^ ((N.factorization (pr v) : ℤ) + a) := by
  set c := ratDirichletLocalChar hχ v
  let π := (ratPrimeUnit v) ^ a
  have hp0 : (0 : ℝ) < pr v := by exact_mod_cast (pr_prime v).pos
  have hπn : ‖(π : v.adicCompletion ℚ)‖ = (pr v : ℝ) ^ (-a) := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, ratPrimeUnit_val, ratPrime_norm, inv_zpow,
      zpow_neg]
  have hπ0 : ‖(π : v.adicCompletion ℚ)‖ ≠ 0 := by rw [hπn]; positivity
  have hscale : F𝔭(v) (unitCharTestFun v c) (π * ξ) =
      (‖(π : v.adicCompletion ℚ)‖⁻¹ : ℝ) • F𝔭(v) (shellTestFun v c a) ξ := by
    unfold tamagawaFourier
    rw [← integral_comp_mul_unit v π (fun z ↦ shellTestFun v c a z * star (ψ𝔭(v) (z * ξ) : ℂ))]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    have e1 : (((ratPrimeUnit v ^ a)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
        ((π : v.adicCompletion ℚ) * y) = y := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    simp only [shellTestFun]
    rw [e1, show (π : v.adicCompletion ℚ) * y * ξ = y * (π * ξ) by ring]
  have hF : F𝔭(v) (shellTestFun v c a) ξ =
      (‖(π : v.adicCompletion ℚ)‖ : ℂ) * F𝔭(v) (unitCharTestFun v c) (π * ξ) := by
    rw [hscale, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hπ0,
      Complex.ofReal_one, one_mul]
  rw [hF, mul_ne_zero_iff, and_iff_right (by exact_mod_cast hπ0),
    unitCharTest_fourier_ne_zero_iff hχ v hv, norm_mul, hπn, zpow_add₀ hp0.ne', zpow_neg,
    zpow_natCast]
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

end Shell


/-! ### Item 6: the Fourier-side box decomposition -/

section BoxDecomposition

local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "BS(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))

/-- A predicate on the target of an inductive tensor product with a finite tensor product holds
everywhere once it holds on pure tensors and is closed under zero, addition and scalars. -/
private theorem tensor_ind {ι : Type*} [Fintype ι]
    {E N : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] N) (P : N → Prop)
    (_h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (r : ℂ) x, P x → P (r • x))
    (hpure : ∀ (a : E) (g : ∀ i, M i), P (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) (x : N) : P x := by
  have key : ∀ y : E ⊗[ℂ] (⨂[ℂ] i, M i), P (e y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      induction b using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        exact (congrArg (fun t ↦ P (e t)) (TensorProduct.tmul_smul r a _)).mpr
          ((congrArg P (map_smul e r _)).mpr (hsmul r _ (hpure a g)))
      | add b c hb hc =>
        exact (congrArg (fun t ↦ P (e t)) (TensorProduct.tmul_add a b c)).mpr
          ((congrArg P (map_add e _ _)).mpr (hadd _ _ hb hc))
    | add y z hy hz => exact (congrArg P (map_add e y z)).mpr (hadd _ _ hy hz)
  exact (congrArg P (e.apply_symm_apply x)).mp (key (e.symm x))

/-- Every S-local test is a finite sum of products of an archimedean test and local tests. -/
theorem exists_tensorRep (S : Finset Vℚ) (k : BS(S)) :
    ∃ (ι : Type) (_ : Fintype ι) (α : ι → B∞) (β : ι → ∀ w : S, SB(w.val)),
      ∀ x : SAdeleRing ℚ S, k (Multiplicative.ofAdd x) =
        ∑ i, α i (Multiplicative.ofAdd x.1) * ∏ w, β i w (Multiplicative.ofAdd (x.2 w)) := by
  classical
  let P : BS(S) → Prop := fun t ↦ ∃ (ι : Type) (_ : Fintype ι) (α : ι → B∞)
    (β : ι → ∀ w : S, SB(w.val)), ∀ x : SAdeleRing ℚ S, t (Multiplicative.ofAdd x) =
      ∑ i, α i (Multiplicative.ofAdd x.1) * ∏ w, β i w (Multiplicative.ofAdd (x.2 w))
  refine tensor_ind (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose P ?_ ?_ ?_ ?_ k
  · refine ⟨Empty, inferInstance, isEmptyElim, isEmptyElim, fun x ↦ ?_⟩
    rw [Fintype.sum_empty]
    rfl
  · rintro t t' ⟨ι, _, α, β, h⟩ ⟨ι', _, α', β', h'⟩
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim α α', Sum.elim β β', fun x ↦ ?_⟩
    change t (Multiplicative.ofAdd x) + t' (Multiplicative.ofAdd x) = _
    rw [h, h', Fintype.sum_sum_type]
    rfl
  · rintro r t ⟨ι, _, α, β, h⟩
    refine ⟨ι, inferInstance, fun i ↦ r • α i, β, fun x ↦ ?_⟩
    change r * t (Multiplicative.ofAdd x) = _
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc]
    rfl
  · intro a g
    refine ⟨Unit, inferInstance, fun _ ↦ a, fun _ ↦ g, fun x ↦ ?_⟩
    have hs := (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose_spec a g x
    refine hs.trans ?_
    simp only [Finset.univ_unique, Finset.sum_singleton]

/-- A Schwartz–Bruhat test on `ℚ_p` is invariant under translation by every small element. -/
private theorem exists_radius_invariant (v : Vℚ) (f : SB(v)) :
    ∃ δ > 0, ∀ x y : v.adicCompletion ℚ, ‖y‖ < δ →
      f (Multiplicative.ofAdd (x + y)) = f (Multiplicative.ofAdd x) := by
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff ℚ v (fun y ↦ f (Multiplicative.ofAdd y))).mp
    ⟨f, fun _ ↦ rfl⟩
  set g : v.adicCompletion ℚ → ℂ := fun y ↦ f (Multiplicative.ofAdd y)
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric (c := fun z : ℂ ↦ g ⁻¹' {z})
    (hcs : IsCompact (tsupport g)) (fun z ↦ hlc.isOpen_fiber z)
    (fun x _ ↦ mem_iUnion.mpr ⟨g x, rfl⟩)
  refine ⟨δ, hδ, fun x y hy ↦ ?_⟩
  change g (x + y) = g x
  have hxy : dist (x + y) x < δ := by rwa [dist_eq_norm, add_sub_cancel_left]
  by_cases hx : x ∈ tsupport g
  · obtain ⟨z, hz⟩ := hcov x hx
    exact (Set.mem_singleton_iff.mp (hz hxy)).trans
      (Set.mem_singleton_iff.mp (hz (Metric.mem_ball_self hδ))).symm
  · by_cases hx' : x + y ∈ tsupport g
    · obtain ⟨z, hz⟩ := hcov (x + y) hx'
      have h2 : dist x (x + y) < δ := by rwa [dist_comm]
      exact (Set.mem_singleton_iff.mp (hz (Metric.mem_ball_self hδ))).trans
        (Set.mem_singleton_iff.mp (hz h2)).symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

private theorem exists_pos_le_all {ι : Type*} [Fintype ι] (δ : ι → ℝ) (h : ∀ j, 0 < δ j) :
    ∃ ρ > 0, ∀ j, ρ ≤ δ j := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun j ↦ isEmptyElim j⟩
  · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ δ Finset.univ_nonempty
    exact ⟨δ j₀, h j₀, fun j ↦ hj₀ j (Finset.mem_univ _)⟩

/-- The closed ball of radius `ρ` in `ℚ_p`, as an additive subgroup (ultrametric). -/
private def ballAddSubgroup (v : Vℚ) (ρ : ℝ) (hρ : 0 ≤ ρ) : AddSubgroup (v.adicCompletion ℚ) where
  carrier := {d | ‖d‖ ≤ ρ}
  add_mem' := fun {a b} ha hb ↦ (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp only [Set.mem_ofPred_eq, norm_zero]; exact hρ
  neg_mem' := fun {a} ha ↦ by simpa only [Set.mem_ofPred_eq, norm_neg] using ha

private theorem mem_ballAddSubgroup (v : Vℚ) (ρ : ℝ) (hρ : 0 ≤ ρ) (d : v.adicCompletion ℚ) :
    d ∈ ballAddSubgroup v ρ hρ ↔ ‖d‖ ≤ ρ := Iff.rfl

private theorem quotient_mk_eq_iff (v : Vℚ) (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : v.adicCompletion ℚ) :
    (QuotientAddGroup.mk a : v.adicCompletion ℚ ⧸ ballAddSubgroup v ρ hρ) = QuotientAddGroup.mk b ↔
      ‖a - b‖ ≤ ρ := by
  rw [QuotientAddGroup.eq, mem_ballAddSubgroup, neg_add_eq_sub, ← neg_sub, norm_neg]

private theorem sb_sum_apply {G : Type*} [CommGroup G] [TopologicalSpace G] {ι : Type*}
    (s : Finset ι) (f : ι → SchwartzBruhat G) (x : G) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- The pointwise decomposition of a test along a finite family of cosets in the finite
coordinates, from invariance on each coset and vanishing off them. -/
private theorem decomp_of_cosets (S : Finset Vℚ) (K : BS(S)) {Q : S → Type}
    [∀ w, DecidableEq (Q w)] (mk : ∀ w : S, w.val.adicCompletion ℚ → Q w)
    (I : Finset (∀ w : S, Q w)) (rep : ∀ w : S, Q w → w.val.adicCompletion ℚ)
    (A : (∀ w : S, Q w) → B∞) (c : ∀ w : S, Q w → SB(w.val)) (E : (∀ w : S, Q w) → BS(S))
    (hE : ∀ q (x : SAdeleRing ℚ S), E q (Multiplicative.ofAdd x) =
      A q (Multiplicative.ofAdd x.1) * ∏ w, c w (q w) (Multiplicative.ofAdd (x.2 w)))
    (hA : ∀ q z, A q (Multiplicative.ofAdd z) =
      K (Multiplicative.ofAdd ((z, fun w ↦ rep w (q w)) : SAdeleRing ℚ S)))
    (hc : ∀ w q ξ, c w q (Multiplicative.ofAdd ξ) = if mk w ξ = q then 1 else 0)
    (hinv : ∀ ξ : SAdeleRing ℚ S, (fun w ↦ mk w (ξ.2 w)) ∈ I →
      K (Multiplicative.ofAdd ((ξ.1, fun w ↦ rep w (mk w (ξ.2 w))) : SAdeleRing ℚ S)) =
        K (Multiplicative.ofAdd ξ))
    (hzero : ∀ ξ : SAdeleRing ℚ S, (fun w ↦ mk w (ξ.2 w)) ∉ I → K (Multiplicative.ofAdd ξ) = 0) :
    K = ∑ q ∈ I, E q := by
  classical
  refine SchwartzBruhat.ext fun x ↦ ?_
  rw [sb_sum_apply]
  obtain ⟨ξ, rfl⟩ : ∃ y : SAdeleRing ℚ S, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  let q₀ : ∀ w : S, Q w := fun w ↦ mk w (ξ.2 w)
  have hterm (q : ∀ w : S, Q w) :
      E q (Multiplicative.ofAdd ξ) = if q₀ = q then A q (Multiplicative.ofAdd ξ.1) else 0 := by
    rw [hE]
    simp only [hc]
    rw [Fintype.prod_boole]
    by_cases hq : q₀ = q
    · rw [ite_eq_left_of_eq_true _ _ (eq_true fun w ↦ congrFun hq w),
        ite_eq_left_of_eq_true _ _ (eq_true hq), mul_one]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hq (funext h)),
        ite_eq_right_of_eq_false _ _ (eq_false hq), mul_zero]
  simp only [hterm, Finset.sum_ite_eq]
  by_cases hq₀ : q₀ ∈ I
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hq₀), hA]
    exact (hinv ξ hq₀).symm
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hq₀)]
    exact hzero ξ hq₀

/-- The Fourier-side cut: a test supported in the box is a finite sum of pure tensors whose
archimedean factors are supported in `|z_∞| ≤ X` and whose local factors are indicators of small
cosets inside `{|ξ| ≤ X}`. -/
private theorem box_decomposition_aux (S : Finset Vℚ) {X : ℝ} (hX : 0 < X) (K : BS(S))
    (hKbox : ∀ ξ : SAdeleRing ℚ S, ξ ∉ sLocalPWBox S X → K (Multiplicative.ofAdd ξ) = 0) :
    ∃ (ι : Type) (I : Finset ι) (A : ι → B∞) (c : ι → ∀ w : S, SB(w.val)),
      (∀ i ∈ I, ∀ z : InfiniteAdeleRing ℚ, A i (Multiplicative.ofAdd z) ≠ 0 →
        |realCoord (z Rat.infinitePlace)| ≤ X) ∧
      (∀ i ∈ I, ∀ w : S, ∀ ξ : w.val.adicCompletion ℚ, c i w (Multiplicative.ofAdd ξ) ≠ 0 →
        ‖ξ‖ ≤ X) ∧
      K = ∑ i ∈ I, (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose
        (A i ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, c i w)) := by
  -- tensor representation and a uniform radius of invariance in the finite coordinates
  have hE := exists_tensorRep S K
  obtain ⟨ι₀, hE⟩ := hE
  obtain ⟨hι₀, hE⟩ := hE
  obtain ⟨α, β, hrep⟩ := hE
  classical
  have hrad (j : ι₀ × S) := exists_radius_invariant j.2.val (β j.1 j.2)
  choose δ hδ hδinv using hrad
  have hρ₀E := exists_pos_le_all δ hδ
  obtain ⟨ρ₀, hρ₀E⟩ := hρ₀E
  obtain ⟨hρ₀, hρ₀le⟩ := hρ₀E
  have hρE : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ X ∧ ∀ j : ι₀ × S, ρ < δ j :=
    ⟨min (ρ₀ / 2) X, lt_min (half_pos hρ₀) hX, min_le_right _ _,
      fun j ↦ (min_le_left _ _).trans_lt ((half_lt_self hρ₀).trans_le (hρ₀le j))⟩
  obtain ⟨ρ, hρE⟩ := hρE
  obtain ⟨hρpos, hρE⟩ := hρE
  obtain ⟨hρX, hρδ⟩ := hρE
  have hKinv (ξ : SAdeleRing ℚ S) (d : ∀ w : S, w.val.adicCompletion ℚ) (hd : ∀ w, ‖d w‖ ≤ ρ) :
      K (Multiplicative.ofAdd ((ξ.1, fun w ↦ ξ.2 w + d w) : SAdeleRing ℚ S)) =
        K (Multiplicative.ofAdd ξ) := by
    rw [hrep, hrep]
    refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (Finset.prod_congr rfl fun w _ ↦ ?_)
    exact hδinv (i, w) (ξ.2 w) (d w) ((hd w).trans_lt (hρδ (i, w)))
  -- cosets of the ball in each finite coordinate
  let H (w : S) := ballAddSubgroup w.val ρ hρpos.le
  let Q (w : S) := w.val.adicCompletion ℚ ⧸ H w
  let B (w : S) : Set (w.val.adicCompletion ℚ) := Metric.closedBall 0 X
  have hdisc (w : S) : DiscreteTopology (Q w) := QuotientAddGroup.discreteTopology (by
    have h : ((H w : AddSubgroup _) : Set (w.val.adicCompletion ℚ)) = Metric.closedBall 0 ρ := by
      ext d
      simp only [SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right]
      rfl
    rw [h]
    exact IsUltrametricDist.isOpen_closedBall _ hρpos.ne')
  have himg (w : S) : (QuotientAddGroup.mk '' B w : Set (Q w)).Finite := by
    let : ProperSpace (w.val.adicCompletion ℚ) := properSpace_adicCompletion w.val
    exact ((isCompact_closedBall _ _).image continuous_quotient_mk').finite_of_discrete
  let T (w : S) : Finset (Q w) := (himg w).toFinset
  let rep (w : S) (q : Q w) : w.val.adicCompletion ℚ :=
    if h : q ∈ QuotientAddGroup.mk '' B w then h.choose else 0
  have hrep_mem (w : S) (q : Q w) (hq : q ∈ T w) : rep w q ∈ B w ∧
      (QuotientAddGroup.mk (rep w q) : Q w) = q := by
    have hq' : q ∈ QuotientAddGroup.mk '' B w := (himg w).mem_toFinset.mp hq
    simp only [rep, hq', ↓reduceDIte]
    exact hq'.choose_spec
  let I : Finset (∀ w : S, Q w) := Fintype.piFinset T
  -- the coset indicators
  let cfun (w : S) (q : Q w) (ξ : w.val.adicCompletion ℚ) : ℂ :=
    if (QuotientAddGroup.mk ξ : Q w) = q then 1 else 0
  have hc_mem (w : S) (q : Q w) :
      ∃ c : SB(w.val), ∀ ξ, c (Multiplicative.ofAdd ξ) = cfun w q ξ := by
    refine (mem_finitePlaceSchwartz_iff ℚ w.val (cfun w q)).mpr ⟨?_, ?_⟩
    · exact (IsLocallyConstant.of_discrete
        (fun t : Q w ↦ if t = q then (1 : ℂ) else 0)).comp_continuous continuous_quotient_mk'
    · obtain ⟨x₀, hx₀⟩ := QuotientAddGroup.mk_surjective q
      let : ProperSpace (w.val.adicCompletion ℚ) := properSpace_adicCompletion w.val
      refine HasCompactSupport.intro (isCompact_closedBall x₀ ρ) fun ξ hξ ↦ ?_
      simp only [cfun, ite_eq_right_iff, one_ne_zero, imp_false]
      intro h
      rw [← hx₀, quotient_mk_eq_iff] at h
      exact hξ (by rwa [Metric.mem_closedBall, dist_eq_norm])
  choose c hc using hc_mem
  -- the archimedean slices
  let evInf (z : InfiniteAdeleRing ℚ) : B∞ →ₗ[ℂ] ℂ :=
    { toFun := fun φ ↦ φ (Multiplicative.ofAdd z)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let A (q : ∀ w : S, Q w) : B∞ :=
    ∑ i, (∏ w, β i w (Multiplicative.ofAdd (rep w (q w)))) • α i
  have hA (q : ∀ w : S, Q w) (z : InfiniteAdeleRing ℚ) :
      A q (Multiplicative.ofAdd z) =
        K (Multiplicative.ofAdd ((z, fun w ↦ rep w (q w)) : SAdeleRing ℚ S)) := by
    change evInf z (A q) = _
    rw [map_sum, hrep]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  -- the decomposition of the transform
  have hinv' (ξ : SAdeleRing ℚ S) (hq : (fun w ↦ (QuotientAddGroup.mk (ξ.2 w) : Q w)) ∈ I) :
      K (Multiplicative.ofAdd ((ξ.1, fun w ↦ rep w (QuotientAddGroup.mk (ξ.2 w))) :
        SAdeleRing ℚ S)) = K (Multiplicative.ofAdd ξ) := by
    have hd : ∀ w, ‖rep w (QuotientAddGroup.mk (ξ.2 w)) - ξ.2 w‖ ≤ ρ := fun w ↦
      (quotient_mk_eq_iff _ _ _ _ _).mp
        (hrep_mem w _ (Fintype.mem_piFinset.mp hq w)).2
    have h := hKinv ξ (fun w ↦ rep w (QuotientAddGroup.mk (ξ.2 w)) - ξ.2 w) hd
    have ht : (fun w ↦ ξ.2 w + (rep w (QuotientAddGroup.mk (ξ.2 w)) - ξ.2 w)) =
        fun w ↦ rep w (QuotientAddGroup.mk (ξ.2 w)) := funext fun w ↦ by ring
    rw [ht] at h
    exact h
  have hzero' (ξ : SAdeleRing ℚ S) (hq : (fun w ↦ (QuotientAddGroup.mk (ξ.2 w) : Q w)) ∉ I) :
      K (Multiplicative.ofAdd ξ) = 0 := by
    apply hKbox
    intro hbox
    apply hq
    refine Fintype.mem_piFinset.mpr fun w ↦ (himg w).mem_toFinset.mpr ⟨ξ.2 w, ?_, rfl⟩
    simpa only [B, Metric.mem_closedBall, dist_zero_right] using hbox.2 w
  have hKdec := decomp_of_cosets S K (fun w ξ ↦ (QuotientAddGroup.mk ξ : Q w)) I rep A
    (fun w q ↦ c w q)
    (fun q ↦ (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose (A q ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, c w (q w))))
    (fun q x ↦ (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose_spec (A q) (fun w ↦ c w (q w)) x)
    hA (fun w q ξ ↦ hc w q ξ) hinv' hzero'
  refine ⟨∀ w : S, Q w, I, A, fun q w ↦ c w (q w), fun q hq z hz ↦ ?_, fun q hq w ξ hξ ↦ ?_, hKdec⟩
  · rw [hA] at hz
    have hbox : ((z, fun w ↦ rep w (q w)) : SAdeleRing ℚ S) ∈ sLocalPWBox S X := by
      by_contra h
      exact hz (hKbox _ h)
    have h1 := hbox.1 Rat.infinitePlace
    have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) (z Rat.infinitePlace)
    change ‖realCoord (z Rat.infinitePlace)‖ = _ at hn
    have hm : Rat.infinitePlace.mult = 1 := by
      simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
    change ‖z Rat.infinitePlace‖ ^ Rat.infinitePlace.mult ≤ X at h1
    rwa [hm, pow_one, ← hn, Real.norm_eq_abs] at h1
  · rw [hc] at hξ
    have hq' : (QuotientAddGroup.mk ξ : Q w) = q w := by
      by_contra h
      exact hξ (ite_eq_right_of_eq_false _ _ (eq_false h))
    obtain ⟨hrB, hrq⟩ := hrep_mem w (q w) (Fintype.mem_piFinset.mp hq w)
    have hd : ‖ξ - rep w (q w)‖ ≤ ρ := (quotient_mk_eq_iff _ _ _ _ _).mp (hq'.trans hrq.symm)
    have hr : ‖rep w (q w)‖ ≤ X := by
      simpa only [B, Metric.mem_closedBall, dist_zero_right] using hrB
    calc ‖ξ‖ = ‖rep w (q w) + (ξ - rep w (q w))‖ := by rw [add_sub_cancel]
      _ ≤ max ‖rep w (q w)‖ ‖ξ - rep w (q w)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ X := max_le hr (hd.trans hρX)

private theorem sFourier_sum_apply (S : Finset Vℚ) {ι : Type*} (I : Finset ι) (F : ι → BS(S))
    (y : SAdeleRing ℚ S) :
    sAdeleSchwartzFourier (∑ i ∈ I, F i) (Multiplicative.ofAdd y) =
      ∑ i ∈ I, sAdeleSchwartzFourier (F i) (Multiplicative.ofAdd y) := by
  obtain ⟨T, hT⟩ := sLocal_fourier_continuousLinear (F := ℚ) (S := S)
  rw [← hT, map_sum, sb_sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hT]

/-- Pulling a Fourier-side decomposition back by Fourier inversion. -/
private theorem pullback_sum (S : Finset Vℚ) (k : BS(S)) {ι : Type*} (I : Finset ι)
    (F G : ι → BS(S)) (hdec : sAdeleSchwartzFourier k = ∑ i ∈ I, F i)
    (hFG : ∀ i ∈ I, ∀ x : SAdeleRing ℚ S,
      sAdeleSchwartzFourier (F i) (Multiplicative.ofAdd (-x)) = G i (Multiplicative.ofAdd x)) :
    k = ∑ i ∈ I, G i := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  rw [sb_sum_apply]
  have hinv := sLocal_fourier_inversion k (-x.toAdd)
  rw [neg_neg] at hinv
  change k (Multiplicative.ofAdd x.toAdd) = ∑ i ∈ I, G i (Multiplicative.ofAdd x.toAdd)
  rw [← hinv, hdec, sFourier_sum_apply]
  exact Finset.sum_congr rfl fun i hi ↦ hFG i hi x.toAdd

/-- An archimedean test over `ℚ` is a real Schwartz function of the archimedean coordinate. -/
private theorem archSB_eq_schwartz (A : B∞) :
    ∃ a : 𝓢(ℝ, ℂ), ∀ z : InfiniteAdeleRing ℚ,
      A (Multiplicative.ofAdd z) = a (realCoord (z Rat.infinitePlace)) := by
  classical
  let : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    uniqueOfSubsingleton ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  let : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.property) (IsTotallyReal.isReal w.val)⟩
  let e := (ContinuousLinearEquiv.prodUnique ℝ
      ({w : InfinitePlace ℚ // w.IsReal} → ℝ) ({w : InfinitePlace ℚ // w.IsComplex} → ℂ)).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : {w : InfinitePlace ℚ // w.IsReal} ↦ ℝ))
  obtain ⟨G, hG⟩ := (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun z : InfiniteAdeleRing ℚ ↦ A (Multiplicative.ofAdd z))).mp A.property
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G, fun z ↦ ?_⟩
  rw [← hG z]
  change G _ = G (e.symm (realCoord (z Rat.infinitePlace)))
  congr 1
  apply e.injective
  rw [e.apply_symm_apply]
  rfl

/-- Paper: (11.3.1.3), p. 494, and Definition 7.3.2.1(1), p. 351, over `ℚ`.
**Item 6: the Fourier-side box decomposition.** An S-local test `k` whose Fourier transform is
supported in the box `sLocalPWBox S X` (`X > 0`) is a finite sum of pure tensors
`archTest (g i) ⊗ ⨂_v b i v` in which every `g i` has Fourier support in `[-X, X]` and every local
factor `b i v` has Fourier transform vanishing on `{|ξ|_v > X}`. The decomposition is made on the
Fourier side: the Fourier transform of `k` is cut along the cosets of a small ball in each finite
coordinate, and every summand is pulled back by `F³ = F⁻¹`.
Deviation: Assumes `0 < X` (the box at a finite place is then a neighbourhood of `0`). -/
theorem sLocalPW_eq_finset_sum_pure (S : Finset Vℚ) {X : ℝ} (hX : 0 < X) (k : BS(S))
    (hk : tsupport (sAdeleSchwartzFourier k).val ⊆
      Multiplicative.toAdd ⁻¹' sLocalPWBox S X) :
    ∃ (ι : Type) (I : Finset ι) (g : ι → 𝓢(ℝ, ℂ)) (b : ι → ∀ w : S, SB(w.val)),
      (∀ i ∈ I, tsupport (fun x : ℝ ↦ (𝓕 (g i)) x) ⊆ Set.Icc (-X) X) ∧
      (∀ i ∈ I, ∀ w : S, ∀ ξ : w.val.adicCompletion ℚ, X < ‖ξ‖ →
        F𝔭(w.val) (fun t ↦ b i w (Multiplicative.ofAdd t)) ξ = 0) ∧
      k = ∑ i ∈ I, (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose
        (archTest (g i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b i w)) := by
  classical
  have hKbox (ξ : SAdeleRing ℚ S) (hξ : ξ ∉ sLocalPWBox S X) :
      sAdeleSchwartzFourier k (Multiplicative.ofAdd ξ) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hξ (hk h))
  have hD := box_decomposition_aux S hX (sAdeleSchwartzFourier k) hKbox
  obtain ⟨ι, hD⟩ := hD
  obtain ⟨I, hD⟩ := hD
  obtain ⟨A, hD⟩ := hD
  obtain ⟨c, hD⟩ := hD
  obtain ⟨hAband, hD⟩ := hD
  obtain ⟨hcband, hdec⟩ := hD
  have ha := fun i ↦ archSB_eq_schwartz (A i)
  choose a ha using ha
  let g : ι → 𝓢(ℝ, ℂ) := fun i ↦ 𝓕⁻ (a i)
  let b : ι → ∀ w : S, SB(w.val) := fun i w ↦
    ratLocalFourierSB w.val (ratLocalFourierSB w.val (ratLocalFourierSB w.val (c i w)))
  have hb (i : ι) (w : S) (t : w.val.adicCompletion ℚ) :
      b i w (Multiplicative.ofAdd t) = F𝔭(w.val) (fun x ↦ c i w (Multiplicative.ofAdd x)) (-t) :=
    ratLocalFourier_inversion w.val (ratLocalFourierSB w.val (c i w)) t
  have hFb (i : ι) (w : S) (ξ : w.val.adicCompletion ℚ) :
      F𝔭(w.val) (fun t ↦ b i w (Multiplicative.ofAdd t)) ξ = c i w (Multiplicative.ofAdd ξ) := by
    have h1 := ratLocalFourier_inversion w.val
      (ratLocalFourierSB w.val (ratLocalFourierSB w.val (c i w))) ξ
    have h2 := ratLocalFourier_inversion w.val (c i w) (-ξ)
    rw [neg_neg] at h2
    exact h1.trans h2
  have hg (i : ι) (r : ℝ) : g i r = 𝓕 (a i) (-r) := by
    simp only [g]
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]
  refine ⟨ι, I, g, b, fun i hi ↦ ?_, fun i hi w ξ hξ ↦ ?_, ?_⟩
  · have hfg : (fun x : ℝ ↦ (𝓕 (g i)) x) = fun x ↦ a i x := by
      simp only [g, FourierTransform.fourier_fourierInv_eq]
    rw [hfg]
    refine closure_minimal (fun r hr ↦ ?_) isClosed_Icc
    let z : InfiniteAdeleRing ℚ := Pi.single Rat.infinitePlace
      ((InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm r)
    have hz : realCoord (z Rat.infinitePlace) = r := by
      simp only [z, Pi.single_eq_same, RingEquiv.apply_symm_apply]
    have hAz : A i (Multiplicative.ofAdd z) ≠ 0 := by rw [ha, hz]; exact hr
    have h := hAband i hi z hAz
    rw [hz] at h
    exact abs_le.mp h
  · rw [hFb]
    by_contra hne
    exact absurd (hcband i hi w ξ hne) (not_le.mpr hξ)
  · refine pullback_sum S k I _ _ hdec fun i _ x ↦ ?_
    refine (ratSLocalFourier_prod S _ (fun z ↦ A i (Multiplicative.ofAdd z))
      (fun w t ↦ c i w (Multiplicative.ofAdd t))
      (fun y ↦ (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose_spec (A i) (fun w ↦ c i w) y)
      (-x)).trans (Eq.trans ?_ ((sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose_spec
        (archTest (g i)) (fun w ↦ b i w) x).symm)
    have hAfun : (fun z : InfiniteAdeleRing ℚ ↦ A i (Multiplicative.ofAdd z)) =
        fun z ↦ a i (realCoord (z Rat.infinitePlace)) := funext (ha i)
    rw [hAfun, ratArchFourier_archTest, archTest_apply, hg]
    congr 1
    · congr 1
      change realCoord (-(x.1 Rat.infinitePlace)) = _
      rw [map_neg]
    · refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [hb]
      rfl

end BoxDecomposition

end RiemannMasullo.Isolated
