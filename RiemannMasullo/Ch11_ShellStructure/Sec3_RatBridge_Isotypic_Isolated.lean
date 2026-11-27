module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_Localb_Isolated

/-!
# The isotypic reduction over ℚ

Workstream B for #7351, stage 3c (items 7–8 of stage 3).

* `IsDirichletThetaRep`: the homogeneous theta of an adelic test is that of a Dirichlet test.
* `dirTest_translate_theta`: translating the Dirichlet test by `∏_v p_v^{a_v}` gives the theta of
  the Dirichlet test of a dilate (deliverable 1).
* `ratIsoSum`: the `c⁻¹`-isotypic part of a local test, as a finite sum over the units modulo a
  small open subgroup, with its theta invariance, its shell expansion and its Fourier band.
* `ratBridge_dirichlet_isotypic`: every test of the absolute Paley–Wiener level has the theta of a
  Dirichlet test in the fixed box of size `ratDirichletBoxShift N X` (item 7).

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal ENNReal SchwartzMap FourierTransform NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

open NumberFieldKB.Chebotarev.RatIdele

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Bℚ" => SchwartzBruhat (Multiplicative 𝔸)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ι" => IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ
local notation "realCoord" =>
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "ν𝔭(" v ")" => finiteLocalAdditiveTamagawaMeasure ℚ v
local notation "ψ𝔭(" v ")" => finiteLocalStandardCharacter ℚ v
local notation "SB(" v ")" => SchwartzBruhat (Multiplicative (HeightOneSpectrum.adicCompletion ℚ v))
local notation "F𝔭(" v ")" => tamagawaFourier ν𝔭(v) ψ𝔭(v)
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)

local instance (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _
local instance : MeasurableSpace (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace ℚ) → w.Completion))
local instance (v : Vℚ) : MeasurableSpace (v.adicCompletion ℚ) := borel _
local instance (v : Vℚ) : MeasurableSpace (v.adicCompletion ℚ)ˣ := borel _
local instance (S : Finset Vℚ) : MeasurableSpace (SAdeleRing ℚ S) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing ℚ × ((v : S) → v.val.adicCompletion ℚ)))

/-! ### Generic helpers -/

section Helpers

private theorem sb_sum_apply' {G : Type*} [CommGroup G] [TopologicalSpace G] {κ : Type*}
    (s : Finset κ) (f : κ → SchwartzBruhat G) (x : G) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

private theorem homTheta_add (ω₁ : PontryaginDual (ideleClassNorm ℚ).ker) (f g : Bℚ) (y : Cℚ) :
    homogeneousAdelicTheta ω₁ (f + g) y =
      homogeneousAdelicTheta ω₁ f y + homogeneousAdelicTheta ω₁ g y :=
  congrArg (fun F : C(Cℚ, ℂ) ↦ F y) (((homogeneousAdelicTheta_isLinear ω₁).mk' _).map_add f g)

private theorem homTheta_smul (ω₁ : PontryaginDual (ideleClassNorm ℚ).ker) (c : ℂ) (f : Bℚ)
    (y : Cℚ) : homogeneousAdelicTheta ω₁ (c • f) y = c * homogeneousAdelicTheta ω₁ f y :=
  congrArg (fun F : C(Cℚ, ℂ) ↦ F y) (((homogeneousAdelicTheta_isLinear ω₁).mk' _).map_smul c f)

private theorem homTheta_zero (ω₁ : PontryaginDual (ideleClassNorm ℚ).ker) (y : Cℚ) :
    homogeneousAdelicTheta ω₁ 0 y = 0 :=
  congrArg (fun F : C(Cℚ, ℂ) ↦ F y) (((homogeneousAdelicTheta_isLinear ω₁).mk' _).map_zero)

private theorem translate_translate' (a b : IdQ) (φ : Bℚ) :
    schwartzBruhatUnitTranslate a (schwartzBruhatUnitTranslate b φ) =
      schwartzBruhatUnitTranslate (a * b) φ := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : 𝔸, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply,
    schwartzBruhatUnitTranslate_apply, mul_inv_rev, Units.val_mul, ← mul_assoc, mul_comm
      (↑b⁻¹ : 𝔸)]

private theorem trivial_on_section (ψ : PontryaginDual Cℚ) (hψ : IsOfFinOrder ψ) (t : ℝ≥0ˣ) :
    ψ (ratNormSection t) = 1 := by
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hψ
  let r := (t : ℝ≥0) ^ ((k : ℝ)⁻¹)
  let u : ℝ≥0ˣ := Units.mk0 r (NNReal.rpow_pos (Units.zero_lt t)).ne'
  have hu : u ^ k = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
  rw [← hu, map_pow, map_pow]
  exact (ContinuousMonoidHom.pow_apply (ψ : Cℚ →ₜ* Circle) k (ratNormSection u)).symm.trans
    (congrArg (fun η : PontryaginDual Cℚ ↦ η (ratNormSection u)) hpow)

end Helpers

/-! ### Theta representatives -/

section Rep

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ

/-- The homogeneous theta of the adelic test `φ` at `k · τ(t)` is `ω(k)⁻¹ · mass` times the twisted
radial theta series of the real test `F`, i.e. that of the Dirichlet test of `F`. -/
def IsDirichletThetaRep (hχ : χ.IsPrimitive) (φ : SchwartzBruhat (Multiplicative 𝔸))
    (F : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker),
    homogeneousAdelicTheta ω φ (k.val * ratNormSection t) =
      (ω k : ℂ)⁻¹ * mass * twistedRadialTheta χ F t

theorem isDirichletThetaRep_dirTest (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ)) :
    IsDirichletThetaRep hχ (dirTest hχ f) f :=
  fun t k ↦ ratBridge_dirichletTest_theta hχ hN f t k

/-- A theta representative identifies the theta with that of the Dirichlet test. -/
theorem IsDirichletThetaRep.eq_dirTest {hχ : χ.IsPrimitive} (hN : 1 < N) {φ : Bℚ}
    {F : 𝓢(ℝ, ℂ)} (h : IsDirichletThetaRep hχ φ F) (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker) :
    homogeneousAdelicTheta ω φ (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ F) (k.val * ratNormSection t) :=
  (h t k).trans (isDirichletThetaRep_dirTest hχ hN F t k).symm

theorem IsDirichletThetaRep.add {hχ : χ.IsPrimitive} (hN : 1 < N) {φ φ' : Bℚ}
    {F F' : 𝓢(ℝ, ℂ)} (h : IsDirichletThetaRep hχ φ F) (h' : IsDirichletThetaRep hχ φ' F') :
    IsDirichletThetaRep hχ (φ + φ') (F + F') := by
  intro t k
  have hs := (hasSum_twistedRadialTheta hχ hN F t).add (hasSum_twistedRadialTheta hχ hN F' t)
  have hs' : HasSum (fun m : ℤ ↦ χ m * (F + F') ((m : ℝ) * t))
      (twistedRadialTheta χ F t + twistedRadialTheta χ F' t) := by
    refine hs.congr_fun fun m ↦ ?_
    simp only [add_apply]
    ring
  rw [homTheta_add, h t k, h' t k,
    show twistedRadialTheta χ (F + F') t = _ from hs'.tsum_eq]
  ring

theorem IsDirichletThetaRep.smul {hχ : χ.IsPrimitive} {φ : Bℚ} {F : 𝓢(ℝ, ℂ)}
    (h : IsDirichletThetaRep hχ φ F) (c : ℂ) : IsDirichletThetaRep hχ (c • φ) (c • F) := by
  intro t k
  rw [homTheta_smul, h t k]
  have e : twistedRadialTheta χ (c • F) t = c * twistedRadialTheta χ F t := by
    unfold twistedRadialTheta
    rw [← tsum_mul_left]
    exact tsum_congr fun m ↦ by simp only [smul_apply, smul_eq_mul]; ring
  rw [e]
  ring

theorem isDirichletThetaRep_zero (hχ : χ.IsPrimitive) : IsDirichletThetaRep hχ 0 0 := by
  intro t k
  rw [homTheta_zero]
  simp [twistedRadialTheta]

theorem IsDirichletThetaRep.sum {hχ : χ.IsPrimitive} (hN : 1 < N) {κ : Type*} (s : Finset κ)
    {φ : κ → Bℚ} {F : κ → 𝓢(ℝ, ℂ)} (h : ∀ i ∈ s, IsDirichletThetaRep hχ (φ i) (F i)) :
    IsDirichletThetaRep hχ (∑ i ∈ s, φ i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isDirichletThetaRep_zero hχ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add hN
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end Rep

/-! ### Deliverable 1: translating the Dirichlet test by prime powers -/

section Translate

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ

/-- The idele `∏_{v ∈ S'} p_v^{a_v}` (with `p_v^{a_v}` at `v` and `1` elsewhere). -/
def ratPrimePowIdele (S' : Finset Vℚ) (a : S' → ℤ) : IdQ :=
  ∏ v : S', ι v.val (ratPrimeUnit v.val ^ a v)

/-- The positive real `∏_{v ∈ S'} p_v^{a_v}`. -/
def ratPrimePowReal (S' : Finset Vℚ) (a : S' → ℤ) : ℝ :=
  ∏ v : S', (pr v.val : ℝ) ^ a v

theorem ratPrimePowReal_pos (S' : Finset Vℚ) (a : S' → ℤ) : 0 < ratPrimePowReal S' a :=
  Finset.prod_pos fun v _ ↦ zpow_pos (by exact_mod_cast (pr_prime v.val).pos) _

private def ratPrimePowNN (S' : Finset Vℚ) (a : S' → ℤ) : ℝ≥0ˣ :=
  ∏ v : S', ratPrimeNN v.val ^ a v

private theorem ratPrimePowNN_coe (S' : Finset Vℚ) (a : S' → ℤ) :
    (((ratPrimePowNN S' a : ℝ≥0ˣ) : ℝ≥0) : ℝ) = ratPrimePowReal S' a := by
  simp only [ratPrimePowNN, ratPrimePowReal, Units.coe_prod, NNReal.coe_prod,
    Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, ratPrimeNN_coe]

private theorem ideleClassNorm_ratPrimePowIdele (S' : Finset Vℚ) (a : S' → ℤ) :
    ideleClassNorm ℚ (QuotientGroup.mk (ratPrimePowIdele S' a)) = (ratPrimePowNN S' a)⁻¹ := by
  let φ : IdQ →* ℝ≥0ˣ := (ideleClassNorm ℚ).comp (QuotientGroup.mk' _)
  change φ (ratPrimePowIdele S' a) = _
  rw [ratPrimePowIdele, map_prod, ratPrimePowNN, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [map_zpow, map_zpow]
  change (ideleClassNorm ℚ (QuotientGroup.mk (ι v.val (ratPrimeUnit v.val)))) ^ a v = _
  rw [ideleClassNorm_ratPrimeUnit, inv_zpow]

/-- The nonzero scalar of `dirTest_translate_theta`: `ψ` at the idele class of `∏ p_v^{a_v}`. -/
def ratTranslateScalar (hχ : χ.IsPrimitive) (S' : Finset Vℚ) (a : S' → ℤ) : ℂ :=
  (ratDirichletIdeleChar hχ (QuotientGroup.mk (ratPrimePowIdele S' a)) : ℂ)

theorem ratTranslateScalar_ne_zero (hχ : χ.IsPrimitive) (S' : Finset Vℚ) (a : S' → ℤ) :
    ratTranslateScalar hχ S' a ≠ 0 :=
  Circle.coe_ne_zero _

/-- Paper: Definition 2.2.5.1, p. 95, and (11.3.1.3), p. 494, over `ℚ`.
**Deliverable 1: translating the Dirichlet test by prime powers.** For any finite set of places
`S'` and any exponents `a : S' → ℤ`, the translate of `dirTest χ g` by the idele `∏ p_v^{a_v}` has
the homogeneous theta of the Dirichlet test of `c_a • g(D_a ·)`, `D_a = ∏ p_v^{a_v}` and `c_a` the
value of `ψ` on that idele class. -/
theorem dirTest_translate_theta (hχ : χ.IsPrimitive) (hN : 1 < N) (S' : Finset Vℚ) (a : S' → ℤ)
    (g : 𝓢(ℝ, ℂ)) :
    IsDirichletThetaRep hχ (schwartzBruhatUnitTranslate (ratPrimePowIdele S' a) (dirTest hχ g))
      (ratTranslateScalar hχ S' a •
        schwartzScale (ratPrimePowReal S' a) (ratPrimePowReal_pos S' a).ne' g) := by
  intro t k
  rw [ratBridge_homogeneousTheta_translate]
  set y : Cℚ := QuotientGroup.mk (ratPrimePowIdele S' a) with hy
  set D := ratPrimePowNN S' a
  have hk' : y⁻¹ * k.val * (ratNormSection D)⁻¹ ∈ (ideleClassNorm ℚ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hy,
      ideleClassNorm_ratPrimePowIdele, ideleClassNorm_ratNormSection,
      show ideleClassNorm ℚ k.val = 1 from k.property, inv_inv, mul_one, mul_inv_cancel]
  let k' : (ideleClassNorm ℚ).ker := ⟨_, hk'⟩
  have heq : QuotientGroup.mk (ratPrimePowIdele S' a)⁻¹ * (k.val * ratNormSection t) =
      k'.val * ratNormSection (D * t) := by
    rw [map_mul ratNormSection, QuotientGroup.mk_inv]
    change y⁻¹ * (k.val * ratNormSection t) =
      y⁻¹ * k.val * (ratNormSection D)⁻¹ * (ratNormSection D * ratNormSection t)
    group
  have hsec := trivial_on_section (ratDirichletIdeleChar hχ)
    (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hχ).choose_spec.1 D
  have hω : ratDirichletNormOneChar hχ k' = (ratDirichletIdeleChar hχ y)⁻¹ *
      ratDirichletNormOneChar hχ k := by
    rw [ratDirichletNormOneChar_apply, ratDirichletNormOneChar_apply]
    change ratDirichletIdeleChar hχ (y⁻¹ * k.val * (ratNormSection D)⁻¹) = _
    rw [map_mul, map_mul, map_inv, map_inv, hsec, inv_one, mul_one]
  have hθ : twistedRadialTheta χ (ratTranslateScalar hχ S' a •
      schwartzScale (ratPrimePowReal S' a) (ratPrimePowReal_pos S' a).ne' g) t =
        ratTranslateScalar hχ S' a * twistedRadialTheta χ g (D * t) := by
    unfold twistedRadialTheta
    rw [← tsum_mul_left]
    refine tsum_congr fun m ↦ ?_
    simp only [smul_apply, schwartzScale_apply, smul_eq_mul, ratPrimePowNN_coe, D]
    ring_nf
  rw [heq, ratBridge_dirichletTest_theta hχ hN, hω, Circle.coe_mul, Circle.coe_inv, mul_inv,
    inv_inv, hθ]
  simp only [ratTranslateScalar, ← hy, Units.val_mul, NNReal.coe_mul]
  ring

end Translate


/-! ### The global test of an archimedean and local factors -/

section Phi

/-- The global test `x ↦ g(x_∞) ∏_{w ∈ S} b_w(x_w) ∏_{v ∉ S} 1_{ℤ_v}(x_v)`. -/
def ratPhi (S : Finset Vℚ) (g : 𝓢(ℝ, ℂ)) (b : ∀ w : S, SB(w.val)) : Bℚ :=
  sAdeleSchwartzToGlobal ℚ S
    ((sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose (archTest g ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)))

open Classical in
theorem ratPhi_apply (S : Finset Vℚ) (g : 𝓢(ℝ, ℂ)) (b : ∀ w : S, SB(w.val)) (x : 𝔸) :
    ratPhi S g b (Multiplicative.ofAdd x) =
      if ∀ w : Vℚ, w ∉ S → x.2 w ∈ w.adicCompletionIntegers ℚ then
        g (realCoord (x.1 Rat.infinitePlace)) * ∏ w : S, b w (Multiplicative.ofAdd (x.2 w.val))
      else 0 := by
  rw [ratPhi, sAdeleSchwartzToGlobal_apply, (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose_spec,
    archTest_apply]
  rfl

theorem ratPhi_ext (S : Finset Vℚ) (φ : Bℚ) (g : 𝓢(ℝ, ℂ)) (b : ∀ w : S, SB(w.val))
    (h : ∀ x : 𝔸, φ (Multiplicative.ofAdd x) = ratPhi S g b (Multiplicative.ofAdd x)) :
    φ = ratPhi S g b :=
  SchwartzBruhat.ext fun x ↦ h x.toAdd

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem dirTest_eq_ratPhi (hχ : χ.IsPrimitive) (g : 𝓢(ℝ, ℂ)) :
    dirTest hχ g = ratPhi (ratDirichletS N) g
      (fun w ↦ unitCharTest w.val (ratDirichletLocalChar hχ w.val)) :=
  SchwartzBruhat.ext fun x ↦ by
    change dirTest hχ g (Multiplicative.ofAdd x.toAdd) = ratPhi _ _ _ (Multiplicative.ofAdd x.toAdd)
    rw [dirTest_apply, ratPhi_apply]
    simp only [unitCharTest_apply]

/-- Components of the product of ideles `∏_{w ∈ S} r_w` (with `r_w` at `w`). -/
private theorem ratProdIdele_mul (S : Finset Vℚ) (r : ∀ w : S, (w.val.adicCompletion ℚ)ˣ)
    (x : 𝔸) :
    realCoord (((↑(∏ w : S, ι w.val (r w)) : 𝔸) * x).1 Rat.infinitePlace) =
        realCoord (x.1 Rat.infinitePlace) ∧
      (∀ w₀ : S, (((↑(∏ w : S, ι w.val (r w)) : 𝔸) * x).2 w₀.val) = r w₀ * x.2 w₀.val) ∧
      ∀ v : Vℚ, v ∉ S → (((↑(∏ w : S, ι w.val (r w)) : 𝔸) * x).2 v) = x.2 v := by
  classical
  set y := ∏ w : S, ι w.val (r w)
  have hreal : realPart y = 1 := by
    simp only [y]
    induction (Finset.univ : Finset S) using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact realPart_one
    | insert a s ha ih => rw [Finset.prod_insert ha, realPart_mul, realPart_ofAdicCompletion, ih,
        one_mul]
  have hcomp (v : Vℚ) : ((↑y : 𝔸) * x).2 v = (compV v y : v.adicCompletion ℚ) * x.2 v := rfl
  refine ⟨?_, fun w₀ ↦ ?_, fun v hv ↦ ?_⟩
  · change realCoord ((↑y : 𝔸).1 Rat.infinitePlace * x.1 Rat.infinitePlace) = _
    rw [map_mul]
    change realPart y * _ = _
    rw [hreal, one_mul]
  · rw [hcomp, map_prod, Fintype.prod_eq_single w₀ fun w hw ↦ compV_ofAdicCompletion_ne
      (fun h ↦ hw (Subtype.ext h.symm)) _, compV_ofAdicCompletion_self]
  · rw [hcomp, map_prod, Finset.prod_eq_one fun w _ ↦ compV_ofAdicCompletion_ne
      (fun h ↦ hv (by rw [h]; exact w.2)) _, Units.val_one, one_mul]

theorem ratUnitScale_lc (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ) (b : SB(v)) :
    IsLocallyConstant (fun x ↦ b (Multiplicative.ofAdd (u.val * x))) ∧
      HasCompactSupport (fun x ↦ b (Multiplicative.ofAdd (u.val * x))) := by
  obtain ⟨hl, hc⟩ := (mem_finitePlaceSchwartz_iff ℚ v (fun y ↦ b (Multiplicative.ofAdd y))).mp
    ⟨b, fun _ ↦ rfl⟩
  exact ⟨hl.comp_continuous (continuous_const.mul continuous_id),
    hc.comp_homeomorph (Homeomorph.mulLeft₀ u.val u.ne_zero)⟩

/-- The local test `x ↦ b(u x)` for a unit `u`. -/
def ratUnitScale (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ) (b : SB(v)) : SB(v) :=
  ((mem_finitePlaceSchwartz_iff ℚ v _).mpr (ratUnitScale_lc v u b)).choose

theorem ratUnitScale_apply (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ) (b : SB(v))
    (x : v.adicCompletion ℚ) :
    ratUnitScale v u b (Multiplicative.ofAdd x) = b (Multiplicative.ofAdd (u.val * x)) :=
  ((mem_finitePlaceSchwartz_iff ℚ v _).mpr (ratUnitScale_lc v u b)).choose_spec x

/-- Scaling every local factor by a unit is translating the global test. -/
theorem ratPhi_unitScale (S : Finset Vℚ) (g : 𝓢(ℝ, ℂ)) (b : ∀ w : S, SB(w.val))
    (r : ∀ w : S, (w.val.adicCompletion ℚ)ˣ) :
    ratPhi S g (fun w ↦ ratUnitScale w.val (r w) (b w)) =
      schwartzBruhatUnitTranslate (∏ w : S, ι w.val (r w))⁻¹ (ratPhi S g b) := by
  classical
  refine (ratPhi_ext S _ g _ fun x ↦ ?_).symm
  rw [schwartzBruhatUnitTranslate_apply, inv_inv, ratPhi_apply, ratPhi_apply]
  obtain ⟨h1, h2, h3⟩ := ratProdIdele_mul S r x
  rw [h1]
  simp only [h2, ratUnitScale_apply]
  have hint : (∀ w : Vℚ, w ∉ S → ((↑(∏ w : S, ι w.val (r w)) : 𝔸) * x).2 w ∈
      w.adicCompletionIntegers ℚ) ↔ ∀ w : Vℚ, w ∉ S → x.2 w ∈ w.adicCompletionIntegers ℚ :=
    forall_congr' fun w ↦ imp_congr_right fun hw ↦ by rw [h3 w hw]
  by_cases hx : ∀ w : Vℚ, w ∉ S → x.2 w ∈ w.adicCompletionIntegers ℚ
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hint.mpr hx)), ite_eq_left_of_eq_true _ _ (eq_true hx)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hx (hint.mp h))),
      ite_eq_right_of_eq_false _ _ (eq_false hx)]

/-- Multilinearity of `ratPhi` in the local factors. -/
theorem ratPhi_sum (S : Finset Vℚ) (g : 𝓢(ℝ, ℂ)) {κ : S → Type*} (s : ∀ w, Finset (κ w))
    (f : ∀ w : S, κ w → SB(w.val)) [DecidableEq S] :
    ratPhi S g (fun w ↦ ∑ i ∈ s w, f w i) =
      ∑ t ∈ Fintype.piFinset s, ratPhi S g (fun w ↦ f w (t w)) := by
  classical
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : 𝔸, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [sb_sum_apply', ratPhi_apply]
  simp only [ratPhi_apply, sb_sum_apply']
  rw [Finset.prod_univ_sum]
  split_ifs
  · rw [Finset.mul_sum]
  · simp

theorem ratPhi_smul (S : Finset Vℚ) (g : 𝓢(ℝ, ℂ)) (b : ∀ w : S, SB(w.val)) (c : S → ℂ) :
    ratPhi S g (fun w ↦ c w • b w) = (∏ w, c w) • ratPhi S g b := by
  classical
  refine (ratPhi_ext S _ g _ fun x ↦ ?_).symm
  change (∏ w, c w) * ratPhi S g b (Multiplicative.ofAdd x) = _
  rw [ratPhi_apply, ratPhi_apply]
  have hsm (w : S) (y : Multiplicative (w.val.adicCompletion ℚ)) : (c w • b w) y = c w * b w y :=
    rfl
  simp only [hsm, Finset.prod_mul_distrib]
  split_ifs <;> ring

end Phi


/-! ### Theta of unit translates -/

section UnitTheta

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ

private theorem norm_unit_eq_one {v : Vℚ} (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) : ‖(u : v.adicCompletion ℚ)‖ = 1 :=
  Valued.toNormedField.norm_eq_one_iff.mpr hu

/-- Translating by a product of local units of valuation one multiplies the homogeneous theta by
the inverse of the product of the local components of `ψ`. -/
theorem homTheta_unitTranslate (hχ : χ.IsPrimitive) (S : Finset Vℚ)
    (r : ∀ w : S, (w.val.adicCompletion ℚ)ˣ) (hr : ∀ w, Valued.v (r w : w.val.adicCompletion ℚ) = 1)
    (φ : Bℚ) (y : Cℚ) :
    homogeneousAdelicTheta ω (schwartzBruhatUnitTranslate (∏ w : S, ι w.val (r w))⁻¹ φ) y =
      (∏ w, ratDirichletLocalChar hχ w.val (r w))⁻¹ * homogeneousAdelicTheta ω φ y := by
  set z := ∏ w : S, ι w.val (r w)
  have hz : ideleClassNorm ℚ (QuotientGroup.mk z) = 1 := by
    let φn : IdQ →* ℝ≥0ˣ := (ideleClassNorm ℚ).comp (QuotientGroup.mk' _)
    change φn z = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun w _ ↦ ?_
    change ideleClassNorm ℚ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ w.val (r w)) = 1
    rw [ideleClassNorm_ofAdicCompletion]
    exact Units.ext (NNReal.coe_injective (by
      change ‖(r w : w.val.adicCompletion ℚ)‖ = 1
      exact norm_unit_eq_one _ (hr w)))
  let h : (ideleClassNorm ℚ).ker := ⟨(QuotientGroup.mk z)⁻¹, by
    rw [MonoidHom.mem_ker, map_inv, hz, inv_one]⟩
  rw [ratBridge_homogeneousTheta_translate, inv_inv,
    show (QuotientGroup.mk z : Cℚ) * y = h.val⁻¹ * y by simp [h],
    homogeneousAdelicTheta_homogeneous]
  congr 1
  rw [ratDirichletNormOneChar_apply]
  change ((ratDirichletIdeleChar hχ (QuotientGroup.mk z)⁻¹ : Circle) : ℂ) = _
  rw [map_inv, Circle.coe_inv, ratDirichletIdeleChar_mk, map_prod, Units.coe_prod]
  congr 1
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [ratDirichletLocalChar_apply]

/-- **Isotypic replacement.** If every local factor `P_w` is the sum over a finite set of local
units `r_w q` of `c_w(r_w q) · b_w(r_w q ·)`, the theta of the global test with the factors `P_w`
is the number of index tuples times that with the factors `b_w`. -/
theorem homTheta_ratPhi_isoReplace (hχ : χ.IsPrimitive) (S : Finset Vℚ) (g : 𝓢(ℝ, ℂ))
    (b : ∀ w : S, SB(w.val)) {Q : S → Type*} [∀ w, Fintype (Q w)]
    (rep : ∀ w : S, Q w → (w.val.adicCompletion ℚ)ˣ)
    (hrep : ∀ w q, Valued.v (rep w q : w.val.adicCompletion ℚ) = 1) (y : Cℚ) :
    homogeneousAdelicTheta ω (ratPhi S g (fun w ↦ ∑ q : Q w,
        ratDirichletLocalChar hχ w.val (rep w q) • ratUnitScale w.val (rep w q) (b w))) y =
      ((∏ w, Fintype.card (Q w) : ℕ) : ℂ) * homogeneousAdelicTheta ω (ratPhi S g b) y := by
  classical
  rw [ratPhi_sum S g (fun w ↦ (Finset.univ : Finset (Q w)))]
  have hterm (t : ∀ w, Q w) :
      ratPhi S g (fun w ↦ ratDirichletLocalChar hχ w.val (rep w (t w)) •
          ratUnitScale w.val (rep w (t w)) (b w)) =
        (∏ w, ratDirichletLocalChar hχ w.val (rep w (t w))) •
          schwartzBruhatUnitTranslate (∏ w : S, ι w.val (rep w (t w)))⁻¹ (ratPhi S g b) := by
    rw [ratPhi_smul, ratPhi_unitScale]
  have hsum : ∀ (T : Finset (∀ w, Q w)), homogeneousAdelicTheta ω (∑ t ∈ T,
      ratPhi S g (fun w ↦ ratDirichletLocalChar hχ w.val (rep w (t w)) •
        ratUnitScale w.val (rep w (t w)) (b w))) y =
        (T.card : ℂ) * homogeneousAdelicTheta ω (ratPhi S g b) y := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [homTheta_zero]
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, homTheta_add, ih, hterm, homTheta_smul,
        homTheta_unitTranslate hχ S _ (fun w ↦ hrep w (a w)), Finset.card_insert_of_notMem ha]
      have hne : (∏ w, ratDirichletLocalChar hχ w.val (rep w (a w))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun w _ ↦ by
          rw [ratDirichletLocalChar_apply]; exact Units.ne_zero _
      rw [← mul_assoc, mul_inv_cancel₀ hne]
      push_cast
      ring
  rw [hsum, Fintype.card_piFinset]
  simp only [Finset.card_univ]

end UnitTheta


/-! ### The local isotypic sum -/

section IsoSum

local notation "UU(" v ")" => ↥((HeightOneSpectrum.adicCompletionIntegers ℚ v).units)

private theorem uu_valued (v : Vℚ) (u : UU(v)) :
    Valued.v (((u : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp u.2

private theorem uu_norm (v : Vℚ) (u : UU(v)) :
    ‖(((u : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ)‖ = 1 :=
  Valued.toNormedField.norm_eq_one_iff.mpr (uu_valued v u)

/-- The subgroup `1 + p^n ℤ_p` of `ℤ_p^×`. -/
def ratUnitBall (v : Vℚ) (n : ℕ) : Subgroup UU(v) where
  carrier := {u | ‖(((u : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) - 1‖ ≤ ((pr v : ℝ) ^ n)⁻¹}
  mul_mem' := by
    intro a b ha hb
    change ‖(((a * b : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤ _
    rw [Subgroup.coe_mul, Units.val_mul,
      show ((a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
          ((b : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1 =
        ((a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
          (((b : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) +
        (((a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rw [norm_mul, uu_norm, one_mul]
    exact hb
  one_mem' := by
    change ‖(((1 : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤ _
    simp only [OneMemClass.coe_one, Units.val_one, sub_self, norm_zero]
    positivity
  inv_mem' := by
    intro a ha
    change ‖(((a⁻¹ : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤ _
    have ha0 := ((a : (v.adicCompletion ℚ)ˣ)).ne_zero
    rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val,
      show (((a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))⁻¹ - 1 =
        (((a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))⁻¹ *
          (1 - ((a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) by
        rw [mul_sub, mul_one, inv_mul_cancel₀ ha0],
      norm_mul, norm_inv, uu_norm, inv_one, one_mul, norm_sub_rev]
    exact ha

instance ratUnitBall_finite (v : Vℚ) (n : ℕ) : Finite (UU(v) ⧸ ratUnitBall v n) := by
  have hUc : IsCompact (((HeightOneSpectrum.adicCompletionIntegers ℚ v).units :
      Set (v.adicCompletion ℚ)ˣ)) :=
    Submonoid.units_isCompact
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have : CompactSpace UU(v) := isCompact_iff_compactSpace.mp hUc
  have hc : Continuous (fun u : UU(v) ↦ (((u : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hopen : IsOpen ((ratUnitBall v n : Subgroup UU(v)) : Set UU(v)) := by
    have h : ((ratUnitBall v n : Subgroup UU(v)) : Set UU(v)) =
        (fun u : UU(v) ↦ (((u : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ)) ⁻¹'
          Metric.closedBall 1 ((pr v : ℝ) ^ n)⁻¹ := by
      ext u
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
      rfl
    rw [h]
    exact (IsUltrametricDist.isOpen_closedBall _ (by
      have : (0 : ℝ) < pr v := by exact_mod_cast (pr_prime v).pos
      positivity)).preimage hc
  have := QuotientGroup.discreteTopology hopen
  exact finite_of_compact_of_discrete

noncomputable instance ratUnitBall_fintype (v : Vℚ) (n : ℕ) : Fintype (UU(v) ⧸ ratUnitBall v n) :=
  Fintype.ofFinite _

/-- The `c⁻¹`-isotypic sum of a local test: `∑_{u ∈ ℤ_p^× / (1 + p^n ℤ_p)} c(u) b(u ·)`. -/
def ratIsoSum (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (n : ℕ) (b : SB(v)) : SB(v) :=
  ∑ q : UU(v) ⧸ ratUnitBall v n,
    c ((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ) •
      ratUnitScale v ((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ) b

theorem ratIsoSum_apply (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (n : ℕ) (b : SB(v))
    (x : v.adicCompletion ℚ) :
    ratIsoSum v c n b (Multiplicative.ofAdd x) =
      ∑ q : UU(v) ⧸ ratUnitBall v n, c ((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ) *
        b (Multiplicative.ofAdd ((((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ)) * x)) := by
  rw [ratIsoSum, sb_sum_apply']
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  change c _ * ratUnitScale v _ b (Multiplicative.ofAdd x) = _
  rw [ratUnitScale_apply]

/-- A local test invariant under multiplication by `1 + p^n ℤ_p`. -/
def IsUnitBallInvariant (v : Vℚ) (n : ℕ) (b : SB(v)) : Prop :=
  ∀ u ∈ ratUnitBall v n, ∀ x : v.adicCompletion ℚ,
    b (Multiplicative.ofAdd ((((u : UU(v)) : (v.adicCompletion ℚ)ˣ)) * x)) =
      b (Multiplicative.ofAdd x)

private theorem quasiChar_ne_zero {v : Vℚ} (c : QuasiCharacter (v.adicCompletion ℚ)ˣ)
    (u : (v.adicCompletion ℚ)ˣ) : c u ≠ 0 := by
  intro h
  have h1 := map_mul c u u⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at h1
  exact one_ne_zero h1

/-- **Equivariance**: `P(u x) = c(u)⁻¹ P(x)` for every unit `u`, if `c` is trivial on
`1 + p^n ℤ_p` and `b` is invariant under it. -/
theorem ratIsoSum_mul (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (n : ℕ) (b : SB(v))
    (hc : ∀ u ∈ ratUnitBall v n, c ((u : UU(v)) : (v.adicCompletion ℚ)ˣ) = 1)
    (hb : IsUnitBallInvariant v n b) (u : UU(v)) (x : v.adicCompletion ℚ) :
    ratIsoSum v c n b (Multiplicative.ofAdd ((((u : UU(v)) : (v.adicCompletion ℚ)ˣ)) * x)) =
      (c ((u : UU(v)) : (v.adicCompletion ℚ)ˣ))⁻¹ * ratIsoSum v c n b (Multiplicative.ofAdd x) := by
  rw [ratIsoSum_apply, ratIsoSum_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk u)) _ _ fun q ↦ ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (ratUnitBall v n) (q.out * u)
  have hq : (QuotientGroup.mk (q.out * u) : UU(v) ⧸ ratUnitBall v n) = q * QuotientGroup.mk u := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [hq] at hh
  simp only [Equiv.coe_mulRight]
  rw [hh]
  have hcu := quasiChar_ne_zero c ((u : UU(v)) : (v.adicCompletion ℚ)ˣ)
  have e1 : (((q.out * u * (h : UU(v)) : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x =
      (((h : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
        ((((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
          ((((u : UU(v)) : (v.adicCompletion ℚ)ˣ)) * x)) := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    ring
  rw [e1, hb h h.2, Subgroup.coe_mul, Subgroup.coe_mul, map_mul c, map_mul c, hc h h.2, mul_one]
  field_simp


private theorem exists_radius_invariant' (v : Vℚ) (f : SB(v)) :
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

/-- A local test is invariant under multiplication by `1 + p^n ℤ_p` for all large `n`. -/
theorem exists_unitBallInvariant (v : Vℚ) (b : SB(v)) (n₀ : ℕ) :
    ∃ n ≥ n₀, IsUnitBallInvariant v n b := by
  obtain ⟨δ, hδ, hinv⟩ := exists_radius_invariant' v b
  obtain ⟨-, hcs⟩ := (mem_finitePlaceSchwartz_iff ℚ v (fun y ↦ b (Multiplicative.ofAdd y))).mp
    ⟨b, fun _ ↦ rfl⟩
  obtain ⟨R, hR⟩ := (hcs : IsCompact _).isBounded.subset_closedBall 0
  have hp1 : (1 : ℝ) < pr v := by exact_mod_cast (pr_prime v).one_lt
  obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt (max R 0 / δ) hp1
  refine ⟨max n₀ n₁, le_max_left _ _, fun u hu x ↦ ?_⟩
  have hu' : ‖(((u : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤
      ((pr v : ℝ) ^ (max n₀ n₁))⁻¹ := hu
  have hpn : ((pr v : ℝ) ^ (max n₀ n₁))⁻¹ ≤ ((pr v : ℝ) ^ n₁)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hp1.le (le_max_right _ _))
  by_cases hx : ‖x‖ ≤ max R 0
  · have hsmall : ‖((((u : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) * x‖ < δ := by
      rw [norm_mul]
      calc _ ≤ ((pr v : ℝ) ^ n₁)⁻¹ * max R 0 :=
            mul_le_mul (hu'.trans hpn) hx (norm_nonneg _) (by positivity)
        _ < δ := by
          rw [inv_mul_lt_iff₀ (by positivity)]
          rwa [div_lt_iff₀ hδ] at hn₁
    rw [show (((u : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x =
      x + ((((u : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) * x by ring]
    exact hinv x _ hsmall
  · have hout (y : v.adicCompletion ℚ) (hy : max R 0 < ‖y‖) : b (Multiplicative.ofAdd y) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ b (Multiplicative.ofAdd y)) fun h ↦ by
        have := hR h
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact absurd (this.trans (le_max_left _ _)) (not_le.mpr hy)
    have hx' := lt_of_not_ge hx
    rw [hout x hx', hout _ (by rw [norm_mul, uu_norm, one_mul]; exact hx')]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The local component of `ψ` is trivial on `1 + p^n ℤ_p` once `n ≥ v_p(N)`. -/
theorem ratDirichletLocalChar_trivial_on_ball (hχ : χ.IsPrimitive) (v : Vℚ) (n : ℕ)
    (hn : N.factorization (pr v) ≤ n) :
    ∀ u ∈ ratUnitBall v n,
      ratDirichletLocalChar hχ v ((u : UU(v)) : (v.adicCompletion ℚ)ˣ) = 1 := by
  intro u hu
  have hu' : ‖(((u : UU(v)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤
      ((pr v : ℝ) ^ n)⁻¹ := hu
  have hp1 : (1 : ℝ) < pr v := by exact_mod_cast (pr_prime v).one_lt
  refine ratDirichletLocalChar_eq_one hχ v _ (uu_valued v u) ?_
  apply Valued.toNormedField.norm_le_one_iff.mp
  rw [norm_div, norm_pow, ratPrime_norm, inv_pow, div_inv_eq_mul]
  calc _ ≤ ((pr v : ℝ) ^ n)⁻¹ * (pr v : ℝ) ^ N.factorization (pr v) :=
        mul_le_mul_of_nonneg_right hu' (by positivity)
    _ ≤ 1 := by
      rw [inv_mul_le_one₀ (by positivity)]
      exact pow_le_pow_right₀ hp1.le hn

private theorem localChar_continuous (v : Vℚ) (ξ : v.adicCompletion ℚ) :
    Continuous fun x : v.adicCompletion ℚ ↦ (ψ𝔭(v) (x * ξ) : ℂ) := by
  obtain ⟨ψc, hψc, -⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom ℚ v
  simp_rw [← hψc]
  exact continuous_subtype_val.comp (ψc.continuous.comp (continuous_ofAdd.comp
    (continuous_id.mul continuous_const)))

private theorem localFourier_integrand_integrable (v : Vℚ) (f : SB(v)) (ξ : v.adicCompletion ℚ) :
    Integrable (fun x ↦ f (Multiplicative.ofAdd x) * star (ψ𝔭(v) (x * ξ) : ℂ)) ν𝔭(v) := by
  let : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  let : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion v
  have : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v
  obtain ⟨-, hcs⟩ := (mem_finitePlaceSchwartz_iff ℚ v (fun y ↦ f (Multiplicative.ofAdd y))).mp
    ⟨f, fun _ ↦ rfl⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (hcs.mul_right)
  exact ((schwartzBruhat_continuous f).comp continuous_ofAdd).mul
    ((localChar_continuous v ξ).star)

/-- Linearity of the local Fourier transform on finite sums of Schwartz–Bruhat tests. -/
private theorem localFourier_sum (v : Vℚ) {κ : Type*} (s : Finset κ) (α : κ → ℂ)
    (f : κ → SB(v)) (ξ : v.adicCompletion ℚ) :
    F𝔭(v) (fun x ↦ ∑ i ∈ s, α i * f i (Multiplicative.ofAdd x)) ξ =
      ∑ i ∈ s, α i * F𝔭(v) (fun x ↦ f i (Multiplicative.ofAdd x)) ξ := by
  unfold tamagawaFourier
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x ↦ by simp only; ring)
  · exact ((localFourier_integrand_integrable v (f i) ξ).const_mul (α i)).congr
      (.of_forall fun x ↦ by simp only; ring)

/-- **Fourier band of the isotypic sum.** If the Fourier transform of `b` vanishes on
`{X < |ξ|}`, so does that of its isotypic sum. -/
theorem ratIsoSum_fourier_band (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (n : ℕ)
    (b : SB(v)) {X : ℝ} (hb : ∀ ξ, X < ‖ξ‖ → F𝔭(v) (fun x ↦ b (Multiplicative.ofAdd x)) ξ = 0)
    (ξ : v.adicCompletion ℚ) (hξ : X < ‖ξ‖) :
    F𝔭(v) (fun x ↦ ratIsoSum v c n b (Multiplicative.ofAdd x)) ξ = 0 := by
  have hfun : (fun x ↦ ratIsoSum v c n b (Multiplicative.ofAdd x)) = fun x ↦
      ∑ q ∈ (Finset.univ : Finset (UU(v) ⧸ ratUnitBall v n)),
        c ((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ) *
          ratUnitScale v ((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ) b (Multiplicative.ofAdd x) := by
    funext x
    rw [ratIsoSum_apply]
    simp only [ratUnitScale_apply]
  rw [hfun, localFourier_sum]
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  set r : (v.adicCompletion ℚ)ˣ := ((q.out : UU(v)) : (v.adicCompletion ℚ)ˣ)
  have hrn : ‖(r : v.adicCompletion ℚ)‖ = 1 := uu_norm v q.out
  have hscale : F𝔭(v) (fun x ↦ ratUnitScale v r b (Multiplicative.ofAdd x)) ξ =
      F𝔭(v) (fun x ↦ b (Multiplicative.ofAdd x)) ((r⁻¹ : (v.adicCompletion ℚ)ˣ) * ξ) := by
    unfold tamagawaFourier
    have h := ratLocal_integral_comp_mul v r hrn
      (fun z ↦ b (Multiplicative.ofAdd z) *
        star (ψ𝔭(v) (z * ((r⁻¹ : (v.adicCompletion ℚ)ˣ) * ξ)) : ℂ))
    refine Eq.trans ?_ h
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [ratUnitScale_apply]
    have e : (r : v.adicCompletion ℚ) * y * ((r⁻¹ : (v.adicCompletion ℚ)ˣ) * ξ) = y * ξ := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
    rw [e]
  have hn' : X < ‖((r⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * ξ‖ := by
    rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, hrn, inv_one, one_mul]
    exact hξ
  rw [hscale, hb _ hn', mul_zero]


/-- The twisted shell `c(x / p^a)⁻¹ 1_{|x| = p^{-a}}` as a Schwartz–Bruhat test. -/
def ratShellSB (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (a : ℤ) : SB(v) :=
  ratUnitScale v ((ratPrimeUnit v ^ a)⁻¹) (unitCharTest v c)

theorem ratShellSB_apply (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (a : ℤ)
    (x : v.adicCompletion ℚ) :
    ratShellSB v c a (Multiplicative.ofAdd x) = shellTestFun v c a x := by
  rw [ratShellSB, ratUnitScale_apply, unitCharTest_apply]
  rfl

private theorem norm_primeUnit_zpow (v : Vℚ) (a : ℤ) :
    ‖((ratPrimeUnit v ^ a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = (pr v : ℝ) ^ (-a) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, ratPrimeUnit_val, ratPrime_norm, inv_zpow, zpow_neg]

private theorem ratNorm_eq_zpow' (v : Vℚ) {η : v.adicCompletion ℚ} (hη : η ≠ 0) :
    ∃ m : ℤ, ‖η‖ = (pr v : ℝ) ^ m := by
  have hv0 : Valued.v η ≠ 0 := (Valuation.ne_zero_iff _).mpr hη
  set k := WithZero.log (Valued.v η)
  have hp0 : (0 : ℝ) < pr v := by exact_mod_cast (pr_prime v).pos
  have hvp : Valued.v (pr v : v.adicCompletion ℚ) = WithZero.exp (-1) := by
    simpa only [Rat.cast_natCast, eq_self, ↓reduceIte] using valued_prime v (pr_prime v)
  have h1 : Valued.v (η * ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) :
      v.adicCompletion ℚ)) = 1 := by
    rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, ratPrimeUnit_val, hvp,
      ← WithZero.exp_log hv0, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
    rw [show k + k * -1 = 0 by ring, WithZero.exp_zero]
  have hn := Valued.toNormedField.norm_eq_one_iff.mpr h1
  rw [norm_mul, norm_primeUnit_zpow, zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hp0.ne')] at hn
  exact ⟨k, hn⟩

private theorem mem_unitsImage_iff'' (v : Vℚ) (y : v.adicCompletion ℚ) :
    y ∈ Units.val '' ((v.adicCompletionIntegers ℚ).units : Set (v.adicCompletion ℚ)ˣ) ↔
      Valued.v y = 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hw
  · intro hy
    have hy0 : y ≠ 0 := fun h ↦ by rw [h, map_zero] at hy; exact zero_ne_one hy
    exact ⟨Units.mk0 y hy0,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hy, rfl⟩

private theorem unitCharTestFun_of_valued_ne (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ)
    {y : v.adicCompletion ℚ} (hy : Valued.v y ≠ 1) : unitCharTestFun v c y = 0 := by
  unfold unitCharTestFun
  exact Set.indicator_of_notMem (fun h ↦ hy ((mem_unitsImage_iff'' v y).mp h)) _

private theorem unitCharTestFun_unit (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ)
    (w : (v.adicCompletion ℚ)ˣ) (hw : Valued.v (w : v.adicCompletion ℚ) = 1) :
    unitCharTestFun v c w = (c w)⁻¹ := by
  unfold unitCharTestFun
  rw [Set.indicator_of_mem ((mem_unitsImage_iff'' v _).mpr hw)]
  simp only [ne_eq, w.ne_zero, not_false_eq_true, ↓reduceDIte, Units.mk0_val]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- Paper: (11.3.1.3), p. 494, local input at `q ∣ N`.
**Shell expansion of the isotypic sum, with the box bound.** At a place `q ∣ N`, the isotypic sum
`P` of a test `b` invariant under `1 + q^n ℤ_q` (`n ≥ e_q`) is a finite combination of the twisted
shells, `P = ∑_{a ∈ A} P(q^a) · shell_a`; if the Fourier transform of `b` vanishes on `{X < |ξ|}`,
every shell that occurs has `q^{e_q + a} ≤ X`. -/
theorem ratIsoSum_shell_expansion (hχ : χ.IsPrimitive) (v : Vℚ) (hv : pr v ∣ N) (n : ℕ)
    (hn : N.factorization (pr v) ≤ n) (b : SB(v)) (hb : IsUnitBallInvariant v n b) {X : ℝ}
    (hbX : ∀ ξ, X < ‖ξ‖ → F𝔭(v) (fun x ↦ b (Multiplicative.ofAdd x)) ξ = 0) :
    ∃ A : Finset ℤ, (∀ a ∈ A, (pr v : ℝ) ^ ((N.factorization (pr v) : ℤ) + a) ≤ X) ∧
      ratIsoSum v (ratDirichletLocalChar hχ v) n b =
        ∑ a ∈ A, ratIsoSum v (ratDirichletLocalChar hχ v) n b
          (Multiplicative.ofAdd ((ratPrimeUnit v ^ a : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ)) •
            ratShellSB v (ratDirichletLocalChar hχ v) a := by
  set c := ratDirichletLocalChar hχ v
  set e := N.factorization (pr v)
  set P := ratIsoSum v c n b
  have hc := ratDirichletLocalChar_trivial_on_ball hχ v n hn
  have hp1 : (1 : ℝ) < pr v := by exact_mod_cast (pr_prime v).one_lt
  have hp0 : (0 : ℝ) < pr v := by linarith
  -- value at zero
  have hP0 : P (Multiplicative.ofAdd 0) = 0 := by
    have hE := exists_ratDirichletLocalChar_ne_one hχ v hv
    obtain ⟨u₀, hE⟩ := hE
    obtain ⟨hu₀, hE⟩ := hE
    obtain ⟨-, hne⟩ := hE
    let u : UU(v) :=
      ⟨u₀, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hu₀⟩
    have h := ratIsoSum_mul v c n b hc hb u 0
    rw [mul_zero] at h
    by_contra h0
    have h1 : (c u₀)⁻¹ = 1 := ((mul_eq_right₀ h0).mp h.symm)
    exact hne (inv_eq_one.mp h1)
  -- vanishing near zero and far away
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff ℚ v (fun y ↦ P (Multiplicative.ofAdd y))).mp
    ⟨P, fun _ ↦ rfl⟩
  have hεE := Metric.isOpen_iff.mp (hlc.isOpen_fiber (P (Multiplicative.ofAdd 0))) 0 rfl
  obtain ⟨ε, hε, hεball⟩ := hεE
  have hsmall (x : v.adicCompletion ℚ) (hx : ‖x‖ < ε) : P (Multiplicative.ofAdd x) = 0 := by
    have h : x ∈ Metric.ball (0 : v.adicCompletion ℚ) ε := by
      rwa [Metric.mem_ball, dist_zero_right]
    exact (hεball h).trans hP0
  obtain ⟨R, hR⟩ := (hcs : IsCompact _).isBounded.subset_closedBall 0
  have hlarge (x : v.adicCompletion ℚ) (hx : R < ‖x‖) : P (Multiplicative.ofAdd x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ P (Multiplicative.ofAdd y)) fun h ↦ by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact absurd this (not_le.mpr hx)
  obtain ⟨K₁, hK₁⟩ := pow_unbounded_of_one_lt R hp1
  obtain ⟨K₂, hK₂⟩ := pow_unbounded_of_one_lt ε⁻¹ hp1
  let A₀ : Finset ℤ := Finset.Icc (-(K₁ : ℤ)) K₂
  -- the pointwise shell expansion
  have hexp (x : v.adicCompletion ℚ) : P (Multiplicative.ofAdd x) =
      ∑ a ∈ A₀, P (Multiplicative.ofAdd ((ratPrimeUnit v ^ a : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ)) * shellTestFun v c a x := by
    by_cases hx0 : x = 0
    · rw [hx0, hP0]
      refine (Finset.sum_eq_zero fun a _ ↦ ?_).symm
      rw [shellTestFun, mul_zero,
        unitCharTestFun_of_valued_ne v c (by rw [map_zero]; exact zero_ne_one),
        mul_zero]
    obtain ⟨m, hm⟩ := ratNorm_eq_zpow' v hx0
    set a₀ := -m
    have hw0 : ((ratPrimeUnit v ^ a₀)⁻¹ : (v.adicCompletion ℚ)ˣ).val * x ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) hx0
    let w : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hw0
    have hwn : ‖(w : v.adicCompletion ℚ)‖ = 1 := by
      rw [Units.val_mk0, norm_mul, Units.val_inv_eq_inv_val, norm_inv, norm_primeUnit_zpow, hm,
        neg_neg, inv_mul_cancel₀ (zpow_ne_zero _ hp0.ne')]
    have hwv : Valued.v (w : v.adicCompletion ℚ) = 1 := Valued.toNormedField.norm_eq_one_iff.mp hwn
    let wU : UU(v) :=
      ⟨w, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hwv⟩
    have hxw : x = (w : v.adicCompletion ℚ) *
        ((ratPrimeUnit v ^ a₀ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
      rw [Units.val_mk0, Units.val_inv_eq_inv_val, mul_comm, ← mul_assoc,
        mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    have hPx : P (Multiplicative.ofAdd x) = (c w)⁻¹ * P (Multiplicative.ofAdd
        ((ratPrimeUnit v ^ a₀ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) := by
      rw [hxw]
      exact ratIsoSum_mul v c n b hc hb wU _
    have hshell (a : ℤ) : shellTestFun v c a x = if a = a₀ then (c w)⁻¹ else 0 := by
      unfold shellTestFun
      split_ifs with ha
      · rw [ha]
        exact unitCharTestFun_unit v c w hwv
      · refine unitCharTestFun_of_valued_ne v c fun h ↦ ha ?_
        have hn1 := Valued.toNormedField.norm_eq_one_iff.mpr h
        rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, norm_primeUnit_zpow, hm, ← zpow_neg,
          neg_neg, ← zpow_add₀ hp0.ne'] at hn1
        have := zpow_right_injective₀ hp0 hp1.ne' (hn1.trans (zpow_zero _).symm)
        simp only [a₀] at this ⊢
        omega
    simp only [hshell, mul_ite, mul_zero, Finset.sum_ite_eq']
    split_ifs with ha₀
    · rw [hPx, mul_comm]
    · have ha₀def : a₀ = -m := rfl
      simp only [A₀, Finset.mem_Icc, not_and_or, not_le] at ha₀
      rcases ha₀ with h | h
      · apply hlarge
        rw [hm]
        calc R < (pr v : ℝ) ^ K₁ := hK₁
          _ = (pr v : ℝ) ^ (K₁ : ℤ) := (zpow_natCast _ _).symm
          _ < (pr v : ℝ) ^ m := zpow_lt_zpow_right₀ hp1 (by omega)
      · apply hsmall
        rw [hm]
        calc (pr v : ℝ) ^ m < (pr v : ℝ) ^ (-(K₂ : ℤ)) := zpow_lt_zpow_right₀ hp1 (by omega)
          _ = ((pr v : ℝ) ^ K₂)⁻¹ := by rw [zpow_neg, zpow_natCast]
          _ < ε := (inv_lt_comm₀ (by positivity) hε).mpr hK₂
  -- the Fourier side
  have hshF (a : ℤ) : (fun x ↦ ratShellSB v c a (Multiplicative.ofAdd x)) = shellTestFun v c a :=
    funext (ratShellSB_apply v c a)
  have hfun : (fun x ↦ P (Multiplicative.ofAdd x)) = fun x ↦ ∑ a ∈ A₀,
      P (Multiplicative.ofAdd ((ratPrimeUnit v ^ a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) *
        ratShellSB v c a (Multiplicative.ofAdd x) :=
    funext fun x ↦ by rw [hexp x]; simp only [ratShellSB_apply]
  have hcoef (a : ℤ) (ha : a ∈ A₀) (hX : X < (pr v : ℝ) ^ ((e : ℤ) + a)) :
      P (Multiplicative.ofAdd ((ratPrimeUnit v ^ a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
        0 := by
    let ξ₀ := ((ratPrimeUnit v ^ (-((e : ℤ) + a)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
    have hξ₀ : ‖ξ₀‖ = (pr v : ℝ) ^ ((e : ℤ) + a) := by rw [norm_primeUnit_zpow, neg_neg]
    have h0 := ratIsoSum_fourier_band v c n b hbX ξ₀ (by rw [hξ₀]; exact hX)
    change F𝔭(v) (fun x ↦ P (Multiplicative.ofAdd x)) ξ₀ = 0 at h0
    rw [hfun, localFourier_sum, Finset.sum_eq_single a] at h0
    · rw [hshF] at h0
      exact (mul_eq_zero.mp h0).resolve_right
        ((shellTestFun_fourier_ne_zero_iff hχ v hv a ξ₀).mpr hξ₀)
    · intro a' _ ha'
      rw [hshF]
      have hz : F𝔭(v) (shellTestFun v c a') ξ₀ = 0 := by
        by_contra hne
        have h1 := (shellTestFun_fourier_ne_zero_iff hχ v hv a' ξ₀).mp hne
        rw [hξ₀] at h1
        have h2 := zpow_right_injective₀ hp0 hp1.ne' h1
        omega
      rw [hz, mul_zero]
    · intro h
      exact absurd ha h
  refine ⟨A₀.filter (fun a ↦ (pr v : ℝ) ^ ((e : ℤ) + a) ≤ X),
    fun a ha ↦ (Finset.mem_filter.mp ha).2, ?_⟩
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : v.adicCompletion ℚ, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [sb_sum_apply', hexp x, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  split_ifs with h
  · change _ = _ * ratShellSB v c a (Multiplicative.ofAdd x)
    rw [ratShellSB_apply]
  · rw [hcoef a ha (lt_of_not_ge h), zero_mul]

end IsoSum


/-! ### Fourier bands of real tests -/

section Band

/-- The real test `f` has Fourier transform supported in `[-R, R]`. -/
def IsFourierBand (R : ℝ) (f : 𝓢(ℝ, ℂ)) : Prop :=
  tsupport (fun x : ℝ ↦ (𝓕 f) x) ⊆ Set.Icc (-R) R

theorem isFourierBand_zero (R : ℝ) : IsFourierBand R 0 := by
  have h : (fun x : ℝ ↦ (𝓕 (0 : 𝓢(ℝ, ℂ))) x) = 0 := by funext x; simp
  rw [IsFourierBand, h, tsupport_zero]
  exact Set.empty_subset _

theorem IsFourierBand.add {R : ℝ} {f g : 𝓢(ℝ, ℂ)} (hf : IsFourierBand R f)
    (hg : IsFourierBand R g) :
    IsFourierBand R (f + g) := by
  have h : (fun x : ℝ ↦ (𝓕 (f + g)) x) = (fun x : ℝ ↦ (𝓕 f) x) + fun x ↦ (𝓕 g) x := by
    funext x; simp
  rw [IsFourierBand, h]
  exact (tsupport_add _ _).trans (Set.union_subset hf hg)

theorem IsFourierBand.smul {R : ℝ} {f : 𝓢(ℝ, ℂ)} (hf : IsFourierBand R f) (c : ℂ) :
    IsFourierBand R (c • f) := by
  have h : (fun x : ℝ ↦ (𝓕 (c • f)) x) = fun x ↦ c • (𝓕 f) x := by funext x; simp
  rw [IsFourierBand, h]
  exact (tsupport_smul_subset_right (fun _ : ℝ ↦ c) (fun x : ℝ ↦ (𝓕 f) x)).trans hf

theorem IsFourierBand.sum {R : ℝ} {κ : Type*} (s : Finset κ) {f : κ → 𝓢(ℝ, ℂ)}
    (h : ∀ i ∈ s, IsFourierBand R (f i)) : IsFourierBand R (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isFourierBand_zero R
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem IsFourierBand.mono {R R' : ℝ} (hRR : R ≤ R') {f : 𝓢(ℝ, ℂ)} (hf : IsFourierBand R f) :
    IsFourierBand R' f :=
  hf.trans (Set.Icc_subset_Icc (by linarith) hRR)

/-- Dilating by `D > 0` multiplies the Fourier band by `D`. -/
theorem IsFourierBand.scale {X D : ℝ} (hD : 0 < D) {g : 𝓢(ℝ, ℂ)} (hg : IsFourierBand X g) :
    IsFourierBand (D * X) (schwartzScale D hD.ne' g) := by
  refine closure_minimal (fun w hw ↦ ?_) isClosed_Icc
  have hw' : (𝓕 (schwartzScale D hD.ne' g)) w ≠ 0 := hw
  rw [fourier_schwartzScale] at hw'
  have h1 : (𝓕 g) (w / D) ≠ 0 := right_ne_zero_of_mul hw'
  have h2 := hg (subset_tsupport _ h1)
  rw [Set.mem_Icc, le_div_iff₀ hD, div_le_iff₀ hD] at h2
  constructor <;> nlinarith [h2.1, h2.2]

end Band

/-! ### Item 7: the box isotypic reduction -/

section Isotypic

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ

local notation "Sχ" => ratDirichletS N
local notation "UU(" v ")" => ↥((HeightOneSpectrum.adicCompletionIntegers ℚ v).units)

/-- The box shift `R(X) = X · ∏_{q ∣ N} q^{⌊log_q X⌋ - e_q}`. -/
def ratDirichletBoxShift (N : ℕ) (X : ℝ) : ℝ :=
  X * ∏ q ∈ N.primeFactors, (q : ℝ) ^ (Nat.log q ⌊X⌋₊ - N.factorization q)

private theorem prod_ratDirichletS (f : ℕ → ℝ) :
    ∏ w : Sχ, f (pr w.val) = ∏ q ∈ N.primeFactors, f q := by
  classical
  rw [Finset.prod_coe_sort (ratDirichletS N) (fun w ↦ f (pr w)), ratDirichletS,
    Finset.prod_image fun p _ p' _ h ↦ Subtype.ext (by
      have := congrArg pr h
      rwa [pr_placeOf, pr_placeOf] at this)]
  rw [← Finset.prod_attach N.primeFactors f]
  exact Finset.prod_congr rfl fun p _ ↦ by rw [pr_placeOf]

private theorem prod_le_prod_of_nonneg {κ : Type*} (s : Finset κ) (f g : κ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hf := h0 a (Finset.mem_insert_self a s)
    have hs := Finset.prod_nonneg fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul (h1 a (Finset.mem_insert_self a s))
      (ih (fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi))
      hs (hf.trans (h1 a (Finset.mem_insert_self a s)))

private theorem exponent_le_log (p : ℕ) (hp : 1 < p) {X : ℝ} (k : ℤ)
    (hk : (p : ℝ) ^ k ≤ X) : k ≤ Nat.log p ⌊X⌋₊ := by
  rcases lt_or_ge k 0 with h | h
  · exact h.le.trans (by positivity)
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast] at hk
    have h1 : p ^ m ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hk)
    exact_mod_cast Nat.le_log_of_pow_le hp h1

/-- The dilation factors of the surviving shells are bounded by `R(X) / X`. -/
private theorem ratPrimePowReal_mul_le (hN : 1 < N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) (t : Sχ → ℤ)
    (ht : ∀ w, (pr w.val : ℝ) ^ ((N.factorization (pr w.val) : ℤ) + t w) ≤ X) :
    ratPrimePowReal Sχ t * X ≤ ratDirichletBoxShift N X := by
  have hXpos : 0 < X := by
    obtain ⟨p, hp⟩ : N.primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr hN
    exact (pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) _).trans_le (hX p hp)
  rw [ratDirichletBoxShift, mul_comm X]
  refine mul_le_mul_of_nonneg_right ?_ hXpos.le
  rw [ratPrimePowReal,
    ← prod_ratDirichletS (fun q ↦ (q : ℝ) ^ (Nat.log q ⌊X⌋₊ - N.factorization q))]
  refine prod_le_prod_of_nonneg _ _ _ (fun w _ ↦ by positivity) fun w _ ↦ ?_
  have hp1 : 1 < pr w.val := (pr_prime w.val).one_lt
  have hdv : pr w.val ∣ N := (mem_ratDirichletS (NeZero.ne N) _).mp w.2
  have he : N.factorization (pr w.val) ≤ Nat.log (pr w.val) ⌊X⌋₊ := by
    have := exponent_le_log (pr w.val) hp1 (X := X) (N.factorization (pr w.val)) (by
      rw [zpow_natCast]
      exact hX _ (Nat.mem_primeFactors.mpr ⟨pr_prime _, hdv, NeZero.ne N⟩))
    exact_mod_cast this
  have h1 := exponent_le_log (pr w.val) hp1 _ (ht w)
  rw [← zpow_natCast, Nat.cast_sub he]
  exact zpow_le_zpow_right₀ (by exact_mod_cast hp1.le) (by omega)

/-- The global test with twisted shells at the places over `N` is a translate of the Dirichlet
test. -/
theorem ratPhi_shell_eq_translate (hχ : χ.IsPrimitive) (g : 𝓢(ℝ, ℂ)) (t : Sχ → ℤ) :
    ratPhi Sχ g (fun w ↦ ratShellSB w.val (ratDirichletLocalChar hχ w.val) (t w)) =
      schwartzBruhatUnitTranslate (ratPrimePowIdele Sχ t) (dirTest hχ g) := by
  rw [dirTest_eq_ratPhi]
  change ratPhi Sχ g (fun w ↦ ratUnitScale w.val ((ratPrimeUnit w.val ^ t w)⁻¹)
    (unitCharTest w.val (ratDirichletLocalChar hχ w.val))) = _
  rw [ratPhi_unitScale]
  congr 1
  simp only [ratPrimePowIdele, map_inv, Finset.prod_inv_distrib, inv_inv]

/-- **The theta of a pure tensor in the box.** For a real test `g` with Fourier support in
`[-X, X]` and local tests `b_w` (`w ∣ N`) with Fourier transforms vanishing on `{X < |ξ|}`, the
global test has the theta of a Dirichlet test whose real test has Fourier support in
`[-R(X), R(X)]`. -/
theorem ratPhi_dirichlet_rep (hχ : χ.IsPrimitive) (hN : 1 < N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) (g : 𝓢(ℝ, ℂ))
    (hg : IsFourierBand X g) (b : ∀ w : Sχ, SB(w.val))
    (hb : ∀ w ξ, X < ‖ξ‖ → F𝔭(w.val) (fun x ↦ b w (Multiplicative.ofAdd x)) ξ = 0) :
    ∃ F : 𝓢(ℝ, ℂ), IsFourierBand (ratDirichletBoxShift N X) F ∧
      IsDirichletThetaRep hχ (ratPhi Sχ g b) F := by
  classical
  have hn := fun w : Sχ ↦ exists_unitBallInvariant w.val (b w) (N.factorization (pr w.val))
  choose n hn hinv using hn
  have hdv (w : Sχ) : pr w.val ∣ N := (mem_ratDirichletS (NeZero.ne N) _).mp w.2
  have hsh := fun w : Sχ ↦ ratIsoSum_shell_expansion hχ w.val (hdv w) (n w) (hn w) (b w) (hinv w)
    (hb w)
  choose A hA hexp using hsh
  let α (w : Sχ) (a : ℤ) : ℂ := ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w)
    (Multiplicative.ofAdd ((ratPrimeUnit w.val ^ a : (w.val.adicCompletion ℚ)ˣ) :
      w.val.adicCompletion ℚ))
  -- the theta of the isotypic sums
  have hθ (y : Cℚ) : homogeneousAdelicTheta ω (ratPhi Sχ g (fun w ↦
      ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w))) y =
        ((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) : ℂ) *
          homogeneousAdelicTheta ω (ratPhi Sχ g b) y :=
    homTheta_ratPhi_isoReplace hχ Sχ g b (Q := fun w ↦ UU(w.val) ⧸ ratUnitBall w.val (n w))
      (fun w q ↦ ((q.out : UU(w.val)) : (w.val.adicCompletion ℚ)ˣ))
      (fun w q ↦ HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp q.out.2) y
  have hcard : ((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos fun w _ ↦ Fintype.card_pos).ne'
  -- the isotypic sums as shells, hence translates of the Dirichlet test
  have hdec : ratPhi Sχ g (fun w ↦ ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w)) =
      ∑ t ∈ Fintype.piFinset A, (∏ w, α w (t w)) •
        schwartzBruhatUnitTranslate (ratPrimePowIdele Sχ t) (dirTest hχ g) := by
    rw [show (fun w ↦ ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w)) =
      fun w ↦ ∑ a ∈ A w, α w a • ratShellSB w.val (ratDirichletLocalChar hχ w.val) a from
        funext hexp, ratPhi_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [ratPhi_smul, ratPhi_shell_eq_translate]
  let F' : 𝓢(ℝ, ℂ) := ∑ t ∈ Fintype.piFinset A, (∏ w, α w (t w)) •
    (ratTranslateScalar hχ Sχ t •
      schwartzScale (ratPrimePowReal Sχ t) (ratPrimePowReal_pos Sχ t).ne' g)
  have hrep' : IsDirichletThetaRep hχ (ratPhi Sχ g (fun w ↦
      ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w))) F' := by
    rw [hdec]
    exact IsDirichletThetaRep.sum hN _ fun t _ ↦ (dirTest_translate_theta hχ hN Sχ t g).smul _
  refine ⟨(((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) : ℂ))⁻¹ • F', ?_, ?_⟩
  · refine IsFourierBand.smul (IsFourierBand.sum _ fun t ht ↦ ?_) _
    refine ((hg.scale (ratPrimePowReal_pos Sχ t)).mono ?_).smul _ |>.smul _
    exact ratPrimePowReal_mul_le hN hX t fun w ↦ hA w (t w) (Fintype.mem_piFinset.mp ht w)
  · intro t k
    have h1 := (hrep'.smul ((((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) :
      ℂ))⁻¹)) t k
    rw [homTheta_smul, hθ, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul] at h1
    exact h1

private theorem transition_refl' (S : Finset Vℚ)
    (k : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    sAdeleSchwartzTransition ℚ (le_rfl : S ⊆ S) k = k := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : SAdeleRing ℚ S, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [sAdeleSchwartzTransition_apply, ite_eq_left_of_eq_true _ _ (eq_true fun w hw ↦ absurd w.2 hw)]

/-- Paper: (11.3.1.3), p. 494, over `ℚ`.
**Item 7: the box isotypic reduction.** For a primitive `χ` of conductor `N > 1` and `X` at least
every `q^{e_q}`, every test `g` of the absolute Paley–Wiener level `primaryDivisorialAbsolutePWTests
ℚ S X` has, on every class `k · τ(t)`, the homogeneous theta of the Dirichlet test of a real test
`f` of parity `χ(-1)` with Fourier support in `[-R(X), R(X)]`,
`R(X) = X · ∏_{q ∣ N} q^{⌊log_q X⌋ - e_q}`. -/
theorem ratBridge_dirichlet_isotypic (hχ : χ.IsPrimitive) (hN : 1 < N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) (g : adelePolarSubspace ℚ)
    (hg : g ∈ primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X) :
    ∃ f : 𝓢(ℝ, ℂ), IsDirichletFixedBoxTest χ (ratDirichletBoxShift N X) f ∧
      ∀ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker),
        homogeneousAdelicTheta ω g.val (k.val * ratNormSection t) =
          homogeneousAdelicTheta ω (dirTest hχ f) (k.val * ratNormSection t) := by
  classical
  have hXpos : 0 < X := by
    obtain ⟨p, hp⟩ : N.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hN
    exact (pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) _).trans_le (hX p hp)
  have hg' : g.val ∈ (sLocalPWTests le_rfl (sLocalPWBox Sχ X)).map (sAdeleSchwartzToGlobal ℚ Sχ) :=
    hg
  obtain ⟨k, hk, hkg⟩ := hg'
  rw [SetLike.mem_coe, mem_sLocalPWTests] at hk
  obtain ⟨k₀, hk₀, hband⟩ := hk
  rw [transition_refl'] at hk₀
  subst hk₀
  have hD := sLocalPW_eq_finset_sum_pure Sχ hXpos k₀ hband.2
  obtain ⟨κ, hD⟩ := hD
  obtain ⟨I, hD⟩ := hD
  obtain ⟨gs, hD⟩ := hD
  obtain ⟨bs, hD⟩ := hD
  obtain ⟨hgs, hD⟩ := hD
  obtain ⟨hbs, hdec⟩ := hD
  have hgsum : g.val = ∑ i ∈ I, ratPhi Sχ (gs i) (bs i) := by
    rw [← hkg, hdec, map_sum]
    rfl
  have hrep := fun i (hi : i ∈ I) ↦ ratPhi_dirichlet_rep hχ hN hX (gs i) (hgs i hi) (bs i)
    (hbs i hi)
  choose F hFband hFrep using hrep
  let G : κ → 𝓢(ℝ, ℂ) := fun i ↦ if h : i ∈ I then F i h else 0
  have hG : IsDirichletThetaRep hχ g.val (∑ i ∈ I, G i) := by
    rw [hgsum]
    exact IsDirichletThetaRep.sum hN _ fun i hi ↦ by
      simp only [G, hi, ↓reduceDIte]; exact hFrep i hi
  have hGband : IsFourierBand (ratDirichletBoxShift N X) (∑ i ∈ I, G i) :=
    IsFourierBand.sum _ fun i hi ↦ by simp only [G, hi, ↓reduceDIte]; exact hFband i hi
  refine ⟨dirichletParityPart χ (∑ i ∈ I, G i),
    isDirichletFixedBoxTest_dirichletParityPart χ hGband, fun t k ↦ ?_⟩
  rw [hG t k, ratBridge_dirichletTest_theta hχ hN, ratBridge_dirichlet_parity hχ hN]

end Isotypic

end RiemannMasullo.Isolated
