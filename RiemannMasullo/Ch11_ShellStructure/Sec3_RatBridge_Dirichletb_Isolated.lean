module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_Dirichleta_Isolated

/-!
# The bridge over ℚ: intertwining and transfer

Workstream B for #7351, stage 5 (continued).

* `ratSectionDilate a f`: the project's dilation of a polar adelic test by the norm section,
  the translate by `canonicalIdeleNormSection ℚ (eᵃ)`.
* `ratBridge_intertwining`: the quotient isomorphism `ratBridge_dirichlet_quotient_iso` carries
  this dilation (on the classes of box tests) to `dirichletQuotSemigroup` (deliverable 3).
* `ratProjSemigroup`: the transported semigroup on the completed project quotient, which by
  `ratBridge_intertwining` is the project's dilation on classes of box tests.
* Transfer to the project quotient (deliverable 4): cardinal lifts by actual box tests
  (`ratBridge_cardinal_lifts`), the unconditional basis (`ratBridge_unconditional_basis`), the
  trace of the convolution operator (`ratBridge_convolution_trace`) and its expression through the
  project's dilation (`ratBridge_convolution_eq_dilation`), and the vanishing trace of the positive
  bump (`ratBridge_positiveBump_trace`).

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal ENNReal SchwartzMap FourierTransform NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

open NumberFieldKB.Chebotarev.RatIdele

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleMeasurableSpaceSec1a

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁ℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Lℚ" => (fun g : Cℚ ↦ Real.log (((ideleClassNorm ℚ g).val : ℝ)))
local notation "massℝ" => (normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal
local notation "RStrip(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "QStrip(" α ", " s ")" => CompactIntervalSobolev μℚ Lℚ (-α) α s
local notation "νR(" α ", " s ")" => intervalSobolevMeasure volume id (-α) α s
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "P₀ℚ" => ↥(adelePolarSubspace ℚ)

/-! ### The project's dilation by the norm section -/

section Dilation

/-- Translation by an idele preserves the polar subspace (re-derived from the private
`taperTranslate_mem` of `Ch05_ThetaZSpaces/Sec5_HiddenTaper`). -/
theorem translate_mem_adelePolarSubspace (u : IdeleGroup (𝓞 ℚ) ℚ) (f : P₀ℚ) :
    schwartzBruhatUnitTranslate u f.val ∈ adelePolarSubspace ℚ := by
  obtain ⟨h₀, hF⟩ := (mem_adelePolarSubspace f.val).mp f.property
  apply (mem_adelePolarSubspace _).mpr
  constructor
  · change f.val (Multiplicative.ofAdd (u.inv * 0)) = 0
    simpa only [mul_zero] using h₀
  · rw [adeleSchwartzFourier_zero_unitTranslate, hF, mul_zero]

/-- The project's dilation of a polar test by the norm section: the translate by the idele
`canonicalIdeleNormSection ℚ (eᵃ)` (of norm `eᵃ`). -/
def ratSectionDilate (a : ℝ) (f : P₀ℚ) : P₀ℚ :=
  ⟨schwartzBruhatUnitTranslate (canonicalIdeleNormSection ℚ (ratExpUnit a)) f.val,
    translate_mem_adelePolarSubspace _ f⟩

/-- The homogeneous theta of the dilated test is the theta of the test at the class shifted by
`e^{-a}` along the norm section. -/
theorem homTheta_ratSectionDilate (ω₁ : PontryaginDual C₁ℚ) (a : ℝ) (f : P₀ℚ) (k : C₁ℚ)
    (t : ℝ≥0ˣ) :
    homogeneousAdelicTheta ω₁ (ratSectionDilate a f).val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω₁ f.val (k.val * ratNormSection ((ratExpUnit a)⁻¹ * t)) := by
  change homogeneousAdelicTheta ω₁ (schwartzBruhatUnitTranslate
    (canonicalIdeleNormSection ℚ (ratExpUnit a)) f.val) _ = _
  rw [ratBridge_homogeneousTheta_translate, QuotientGroup.mk_inv, ← ratNormSection_apply,
    map_mul ratNormSection, map_inv ratNormSection]
  exact congrArg (homogeneousAdelicTheta ω₁ f.val) (mul_left_comm _ _ _)

theorem twistedRadialTheta_schwartzScale {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (f₀ : 𝓢(ℝ, ℂ)) (c : ℝ) (hc : c ≠ 0) (r : ℝ) :
    twistedRadialTheta χ (schwartzScale c hc f₀) r = twistedRadialTheta χ f₀ (c * r) := by
  unfold twistedRadialTheta
  refine tsum_congr fun m ↦ ?_
  rw [schwartzScale_apply]
  ring_nf

end Dilation

/-! ### Deliverable 3: intertwining -/

section Intertwining

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ
local notation "Sχ" => ratDirichletS N
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)
local notation "Xr(" X ", " T ")" => ratDirichletBoxShift N X * ∏ q ∈ Finset.image pr T, (q : ℝ)

/-- The prime of a place outside `T` is not a prime of `T`. -/
theorem ratPrime_notMem_image {T : Finset Vℚ} {v : Vℚ} (hvT : v ∉ T) : pr v ∉ T.image pr :=
  fun h ↦ by
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
    exact hvT (pr_injective hwv ▸ hw)

private theorem mass_ne_zero'' : mass ≠ 0 := Complex.ofReal_ne_zero.mpr ratMass_pos.ne'

/-- If the theta of a polar test is that of `dirTest f₀`, the theta of its dilation by
`σ(eᵃ)` is that of `dirTest (f₀(e^{-a} ·))`. -/
theorem homTheta_ratSectionDilate_dirTest (hχ : χ.IsPrimitive) (hN : 1 < N) (f : P₀ℚ)
    (f₀ : 𝓢(ℝ, ℂ))
    (hgf : ∀ (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω f.val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ f₀) (k.val * ratNormSection t)) (a : ℝ)
    (t : ℝ≥0ˣ) (k : C₁ℚ) :
    homogeneousAdelicTheta ω (ratSectionDilate a f).val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ (schwartzScale (Real.exp (-a)) (Real.exp_pos _).ne' f₀))
        (k.val * ratNormSection t) := by
  rw [homTheta_ratSectionDilate, hgf, ratBridge_dirichletTest_theta hχ hN,
    ratBridge_dirichletTest_theta hχ hN, twistedRadialTheta_schwartzScale]
  congr 2
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv,
    ratExpUnit_coe, Real.exp_neg]

/-- **Core identity for unit-invariant tests.** As `halfThetaMap_principalValue_of_mem`, for any
polar test invariant under the local units at the places of `T`. -/
theorem halfThetaMap_principalValue_of_inv (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) (φ : P₀ℚ) (hφ : ∀ v ∈ T, IsLocalUnitInvariant v φ.val)
    (f₀ : 𝓢(ℝ, ℂ))
    (hgf : ∀ (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω φ.val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ f₀) (k.val * ratNormSection t))
    (hmem : MemLp (dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f₀)) 2 (νR(α, s))) :
    j (adelePolarPrincipalValue T φ) =
      ratStripEmbed ω α s (mass • toDirichletStrip α s _ hmem) := by
  refine halfThetaMap_eq_embed ω hj _ mass hmem (EventuallyEq.of_eq (funext fun x ↦ ?_))
  have h := ratBridge_principalValue_general hχ T hT φ.val hφ _ (twistedRadialTheta χ f₀)
    (fun t k ↦ (hgf t k).trans (ratBridge_dirichletTest_theta hχ hN f₀ t k))
    (ratNormOnePart x) (Lℚ x)
  rw [ratNormOnePart_mul] at h
  exact h

open Classical in
/-- The projected image of a unit-invariant test with a Dirichlet theta, and its image under the
quotient isomorphism. -/
theorem ratBridge_quot_iso_proj (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (φ : P₀ℚ) (hφ : ∀ w ∈ T, IsLocalUnitInvariant w φ.val) (f₀ : 𝓢(ℝ, ℂ))
    (hgf : ∀ (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω φ.val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ f₀) (k.val * ratNormSection t))
    (hmem : MemLp (dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f₀)) 2 (νR(α, s)))
    (hE : toDirichletStrip α s _ hmem ∈ dirichletStageSpace χ (T.image pr) Xr(X, T) α s hα hs) :
    ∃ hQ : (ratProjNextStage Sχ ω j T (insert v T) X)ᗮ.starProjection
        (j (adelePolarPrincipalValue T φ)) ∈ ratProjQuot Sχ ω j T (insert v T) X,
      ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX ⟨_, hQ⟩ =
        dirichletStageQuotMap hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v)
          (ratPrime_notMem_image hvT)
          (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
          ⟨toDirichletStrip α s _ hmem, hE⟩ := by
  set q := dirichletStageQuotMap hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v)
    (ratPrime_notMem_image hvT)
    (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
    ⟨toDirichletStrip α s _ hmem, hE⟩ with hq
  have hval : (ratProjNextStage Sχ ω j T (insert v T) X)ᗮ.starProjection
      (j (adelePolarPrincipalValue T φ)) = mass • ratStripEmbed ω α s (q : RStrip(α, s)) := by
    rw [halfThetaMap_principalValue_of_inv hχ hN hj T hT φ hφ f₀ hgf hmem, map_smul, map_smul,
      starProjection_orthogonal_ratStripEmbed ω _ _
        (ratBridge_stage_eq_next hχ hN hα hs hj T hT hvT hv hX), hq,
      coe_dirichletStageQuotMap]
  have hQ := hval ▸ ratBridge_quot_mem hχ hN hα hs hj T hT hvT hv hX q.1 q.2
  refine ⟨hQ, (ContinuousLinearEquiv.eq_symm_apply _).mp (Subtype.ext ?_)⟩
  rw [ratBridge_dirichlet_quotient_iso_symm_apply]
  exact hval

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 3: intertwining.** For a box test `f` and `a ≥ 0`, the class of the project's
dilation `ratSectionDilate a f` (the translate by `canonicalIdeleNormSection ℚ (eᵃ)`) in the
completed quotient is sent by the quotient isomorphism to `dirichletQuotSemigroup a` applied to the
image of the class of `f`. -/
theorem ratBridge_intertwining (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (f : primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X) {a : ℝ} (ha : 0 ≤ a) :
    ∃ hQ : (ratProjNextStage Sχ ω j T (insert v T) X)ᗮ.starProjection
        (j (adelePolarPrincipalValue T (ratSectionDilate a f.val))) ∈
          ratProjQuot Sχ ω j T (insert v T) X,
      ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX ⟨_, hQ⟩ =
        dirichletQuotSemigroup hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v)
          (ratPrime_notMem_image hvT)
          (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs a ha
          (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX
            ⟨ratProjQuotMap Sχ ω j T (insert v T) X f, ratProjQuotMap_mem _ _ _ _ _ _ f⟩) := by
  have hprod := ratPrimes_prod_pos T
  have hR := ratDirichletBoxShift_pos hN hX
  have hTpos : ∀ q ∈ T.image pr, 0 < q := fun q hq ↦ (ratPrimes_spec T hT q hq).1.pos
  have hdiv : (ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) / ∏ q ∈ T.image pr, (q : ℝ) =
      ratDirichletBoxShift N X := mul_div_cancel_right₀ _ hprod.ne'
  obtain ⟨f₀, hbox, hgf⟩ := ratBridge_dirichlet_isotypic hχ hN hX f.val f.property
  have hmem := dirichletDeplete_memLp hχ hN (T.image pr) hTpos hR hα hs hbox (α := α) (s := s)
  have hE := mem_dirichletStageSpace_of_test (T.image pr) hα hs (X := Xr(X, T))
    (by rw [hdiv]; exact hbox) hmem
  obtain ⟨hboxa, hshift⟩ := backHalfShiftCLM_apply_depleted_scale hχ hN (T.image pr) hTpos hR hα hs
    hbox a ha
  have hmema := dirichletDeplete_memLp hχ hN (T.image pr) hTpos hR hα hs hboxa (α := α) (s := s)
  have hEa := mem_dirichletStageSpace_of_test (T.image pr) hα hs (X := Xr(X, T))
    (by rw [hdiv]; exact hboxa) hmema
  have hinv : ∀ w ∈ T, IsLocalUnitInvariant w (ratSectionDilate a f.val).val := fun w hw ↦
    (isLocalUnitInvariant_of_mem_absolutePWTests f.val f.property
      (notMem_ratDirichletS_of_coprime (hT w hw))).translate _
  obtain ⟨hQ, hΦ⟩ := ratBridge_quot_iso_proj hχ hN hα hs hj T hT hvT hv hX
    (ratSectionDilate a f.val) hinv _ (homTheta_ratSectionDilate_dirTest hχ hN f.val f₀ hgf a)
    hmema hEa
  refine ⟨hQ, ?_⟩
  rw [hΦ, ratBridge_dirichlet_quotient_iso_quotMap hχ hN hα hs hj T hT hvT hv hX f f₀ hgf hmem hE,
    dirichletQuotSemigroup_quotMap]
  congr 1
  exact Subtype.ext (hshift hmem hmema).symm

end Intertwining


/-! ### Nuclear operators under an isomorphism of Hilbert spaces -/

section Nuclear

/-- Pre- and postcomposition of a nuclear operator between Banach spaces is nuclear (through the
Banach-series characterization `isNuclearOperator_iff_isBanachNuclear`). -/
private theorem isNuclearOperator_comp_comp' {W X Y Z : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    {A : X →L[ℂ] Y} (hA : IsNuclearOperator A) (S : W →L[ℂ] X) (R : Y →L[ℂ] Z) :
    IsNuclearOperator (R.comp (A.comp S)) := by
  rw [isNuclearOperator_iff_isBanachNuclear] at hA ⊢
  obtain ⟨c, φ, y, hc, hφ, hy, h⟩ := hA
  refine ⟨c, fun n ↦ (φ n).comp S, fun n ↦ R (y n), hc, ?_, ?_, fun x ↦ ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero] at hφ ⊢
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ContinuousLinearMap.opNorm_comp_le _ _) ?_
    simpa using hφ.mul_const ‖S‖
  · have h0 := (R.continuous.tendsto 0).comp hy
    rw [map_zero] at h0
    exact h0
  · simpa only [ContinuousLinearMap.comp_apply, map_smul] using R.hasSum (h (S x))

private theorem nuclearTrace_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hE : HasApproximationProperty E) {A B : E →L[ℂ] E} (h : A = B)
    (hA : IsNuclearOperator A) (hB : IsNuclearOperator B) :
    nuclearTrace hE A hA = nuclearTrace hE B hB := by
  subst h
  rfl

/-- Conjugating a nuclear operator by a continuous linear equivalence of Hilbert spaces gives a
nuclear operator with the same trace. -/
theorem hilbertTrace_conj_equiv {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (e : H₁ ≃L[ℂ] H₂) (A : H₂ →L[ℂ] H₂) (hA : IsNuclearOperator A) :
    ∃ hB : IsNuclearOperator (e.symm.toContinuousLinearMap.comp (A.comp e.toContinuousLinearMap)),
      hilbertTrace ⟨_, hB⟩ = hilbertTrace ⟨A, hA⟩ := by
  have hB := isNuclearOperator_comp_comp' hA e.toContinuousLinearMap e.symm.toContinuousLinearMap
  refine ⟨hB, ?_⟩
  have hA₀ : IsNuclearOperator (e.symm.toContinuousLinearMap.comp A) := by
    have h := isNuclearOperator_comp_comp' hA (ContinuousLinearMap.id ℂ H₂)
      e.symm.toContinuousLinearMap
    rwa [ContinuousLinearMap.comp_id] at h
  have hf := nuclearTrace_factor_comps (hilbert_approximationProperty (H := H₁))
    (hilbert_approximationProperty (H := H₂)) e.toContinuousLinearMap e.injective _ hA₀
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  refine (nuclearTrace_congr _ (by rfl) _ _).trans (hf.trans (nuclearTrace_congr _ ?_ _ _))
  ext x
  simp

/-- Paper: Definition C.3.4.2(2), p. 697. **The trace norm is invariant under unitary
conjugation between two Hilbert spaces.** For `U : H₁ ≃ₗᵢ[ℂ] H₂`, the Gram square root of
`U⁻¹ A U` is `U⁻¹ √(A*A) U` (uniqueness of the positive square root), and the diagonal sum in
the basis `U⁻¹ b` is the diagonal sum of `√(A*A)` in `b` (`hasSum_traceNorm_diagonal`). -/
theorem traceNorm_conj_unitary {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (U : H₁ ≃ₗᵢ[ℂ] H₂) (A : H₂ →L[ℂ] H₂) (hA : IsNuclearOperator A)
    (hB : IsNuclearOperator
      (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (A.comp U.toContinuousLinearEquiv.toContinuousLinearMap))) :
    traceNorm ⟨_, hB⟩ = traceNorm ⟨A, hA⟩ := by
  classical
  set Uc : H₁ →L[ℂ] H₂ := U.toContinuousLinearEquiv.toContinuousLinearMap with hUc
  set Us : H₂ →L[ℂ] H₁ := U.symm.toContinuousLinearEquiv.toContinuousLinearMap with hUs
  set B := Us.comp (A.comp Uc) with hBdef
  set S := CFC.sqrt (A.adjoint * A) with hSdef
  have hUcadj : Uc.adjoint = Us := U.adjoint_eq_symm
  have hUsadj : Us.adjoint = Uc := by
    have h := U.symm.adjoint_eq_symm
    rwa [LinearIsometryEquiv.symm_symm] at h
  have hBadj : B.adjoint = Us.comp (A.adjoint.comp Uc) := by
    rw [hBdef, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hUcadj, hUsadj,
      ContinuousLinearMap.comp_assoc]
  have hApos : 0 ≤ A.adjoint * A := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self A)
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg _
  have hSS : S * S = A.adjoint * A := CFC.sqrt_mul_sqrt_self _ hApos
  have hS1 : 0 ≤ Us.comp (S.comp Uc) := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ← hUsadj]
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hS0).conj_adjoint Us
  have hUU (y : H₂) : Uc (Us y) = y := U.apply_symm_apply y
  have hsq : CFC.sqrt (B.adjoint * B) = Us.comp (S.comp Uc) := by
    refine CFC.sqrt_unique ?_ hS1
    rw [hBadj]
    ext x
    have h := congrArg (fun T : H₂ →L[ℂ] H₂ ↦ Us (T (Uc x))) hSS
    simp only [mul_apply_eq_comp] at h
    simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hUU, hBdef]
    exact h
  obtain ⟨w, b₂, -⟩ := exists_hilbertBasis ℂ H₂
  let b₁ : HilbertBasis w ℂ H₁ := HilbertBasis.ofRepr (U.trans b₂.repr)
  have hb₁ (i : w) : b₁ i = Us (b₂ i) := by
    rw [← HilbertBasis.repr_symm_single b₁, ← HilbertBasis.repr_symm_single b₂]
    rfl
  have h1 : HasSum (fun i ↦ (inner ℂ (b₁ i) (CFC.sqrt (B.adjoint * B) (b₁ i))).re)
      (traceNorm ⟨B, hB⟩) := hasSum_traceNorm_diagonal b₁ ⟨B, hB⟩
  have h2 : HasSum (fun i ↦ (inner ℂ (b₂ i) (S (b₂ i))).re) (traceNorm ⟨A, hA⟩) :=
    hasSum_traceNorm_diagonal b₂ ⟨A, hA⟩
  refine h1.unique (h2.congr_fun fun i ↦ ?_)
  rw [hsq, hb₁, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hUU]
  change (inner ℂ (U.symm (b₂ i)) (U.symm (S (b₂ i)))).re = _
  rw [LinearIsometryEquiv.inner_map_map]

/-- A continuous linear equivalence that multiplies norms by `c⁻¹` (`‖y‖ = c ‖Φ y‖`), scaled by
`c`, as a linear isometry equivalence. -/
def scaledIsometryEquiv {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (Φ : E ≃L[ℂ] F) (c : ℝ) (hc : 0 < c)
    (h : ∀ y, ‖y‖ = c * ‖Φ y‖) : E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (c : ℂ) • Φ.toLinearMap
      norm_map' := fun y ↦ by
        change ‖(c : ℂ) • Φ y‖ = ‖y‖
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le, ← h] }
    fun z ↦ ⟨(c : ℂ)⁻¹ • Φ.symm z, by
      change (c : ℂ) • Φ ((c : ℂ)⁻¹ • Φ.symm z) = z
      rw [map_smul, Φ.apply_symm_apply, smul_smul,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul]⟩

/-- Conjugation by the scaled isometry is conjugation by `Φ`. -/
theorem scaledIsometryEquiv_conj {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (Φ : E ≃L[ℂ] F) (c : ℝ) (hc : 0 < c)
    (h : ∀ y, ‖y‖ = c * ‖Φ y‖) (A : F →L[ℂ] F) :
    (scaledIsometryEquiv Φ c hc h).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (A.comp (scaledIsometryEquiv Φ c hc h).toContinuousLinearEquiv.toContinuousLinearMap) =
      Φ.symm.toContinuousLinearMap.comp (A.comp Φ.toContinuousLinearMap) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsymm (z : F) : (scaledIsometryEquiv Φ c hc h).symm z = (c : ℂ)⁻¹ • Φ.symm z := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    change z = (c : ℂ) • Φ ((c : ℂ)⁻¹ • Φ.symm z)
    rw [map_smul, Φ.apply_symm_apply, smul_smul, mul_inv_cancel₀ hc', one_smul]
  ext x
  change (scaledIsometryEquiv Φ c hc h).symm (A ((c : ℂ) • Φ x)) = Φ.symm (A (Φ x))
  rw [hsymm, map_smul, map_smul, smul_smul, inv_mul_cancel₀ hc', one_smul]

/-- The trace norm is invariant under conjugation by a continuous linear equivalence of Hilbert
spaces that multiplies all norms by the same constant. -/
theorem traceNorm_conj_scaled {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (Φ : E ≃L[ℂ] F) (c : ℝ) (hc : 0 < c) (h : ∀ y, ‖y‖ = c * ‖Φ y‖) (A : F →L[ℂ] F)
    (hA : IsNuclearOperator A)
    (hB : IsNuclearOperator (Φ.symm.toContinuousLinearMap.comp (A.comp Φ.toContinuousLinearMap))) :
    traceNorm ⟨_, hB⟩ = traceNorm ⟨A, hA⟩ := by
  have heq := scaledIsometryEquiv_conj Φ c hc h A
  have hB' := heq ▸ hB
  have hsub : (⟨_, hB⟩ : nuclearEndomorphisms E) = ⟨_, hB'⟩ := Subtype.ext heq.symm
  rw [hsub]
  exact traceNorm_conj_unitary (scaledIsometryEquiv Φ c hc h) A hA hB'

end Nuclear

/-! ### Deliverable 4: transfer to the project quotient -/

section Transfer

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ
local notation "Sχ" => ratDirichletS N
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)
local notation "Xr(" X ", " T ")" => ratDirichletBoxShift N X * ∏ q ∈ Finset.image pr T, (q : ℝ)

instance instCompleteSpaceRatProjQuot (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ) :
    CompleteSpace (ratProjQuot S ω₁ j T Tp X) := by
  unfold ratProjQuot
  exact ((Submodule.isClosed_topologicalClosure _).inter
    (Submodule.isClosed_orthogonal _)).completeSpace_coe

open Classical in
/-- The semigroup on the completed project quotient transported from `dirichletQuotSemigroup`; by
`ratProjSemigroup_quotMap` it is the project's dilation `ratSectionDilate` on classes of box
tests. -/
def ratProjSemigroup (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (a : ℝ) (ha : 0 ≤ a) :
    ratProjQuot Sχ ω j T (insert v T) X →L[ℂ] ratProjQuot Sχ ω j T (insert v T) X :=
  (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).symm.toContinuousLinearMap.comp
    ((dirichletQuotSemigroup hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v)
      (ratPrime_notMem_image hvT)
      (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs a ha).comp
      (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).toContinuousLinearMap)

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`. The transported semigroup is the
project's dilation by the norm section on the classes of box tests. -/
theorem ratProjSemigroup_quotMap (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (f : primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X) {a : ℝ} (ha : 0 ≤ a) :
    ∃ hQ : (ratProjNextStage Sχ ω j T (insert v T) X)ᗮ.starProjection
        (j (adelePolarPrincipalValue T (ratSectionDilate a f.val))) ∈
          ratProjQuot Sχ ω j T (insert v T) X,
      ratProjSemigroup hχ hN hα hs hj T hT hvT hv hX a ha
          ⟨ratProjQuotMap Sχ ω j T (insert v T) X f, ratProjQuotMap_mem _ _ _ _ _ _ f⟩ =
        ⟨_, hQ⟩ := by
  obtain ⟨hQ, h⟩ := ratBridge_intertwining hχ hN hα hs hj T hT hvT hv hX f ha
  refine ⟨hQ, ?_⟩
  exact (ContinuousLinearEquiv.symm_apply_eq _).mpr h.symm

open Classical in
/-- The convolution operator `dirichletConvolutionOp Φ` transported to the completed project
quotient by the quotient isomorphism. -/
def ratProjConvolutionOp (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (Φ : 𝓢(ℝ, ℂ)) :
    ratProjQuot Sχ ω j T (insert v T) X →L[ℂ] ratProjQuot Sχ ω j T (insert v T) X :=
  (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).symm.toContinuousLinearMap.comp
    ((dirichletConvolutionOp hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v) hv
      (ratPrime_notMem_image hvT)
      (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs Φ).comp
      (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).toContinuousLinearMap)

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 4, trace expansion.** The convolution operator transported to the completed
project quotient is nuclear, and its trace is the sum of the eigenvalues
`dirichletConvEigenvalue χ p Φ j` (from `dirichletFixedBox_convolution_trace_expansion`). -/
theorem ratBridge_convolution_trace (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (Φ : 𝓢(ℝ, ℂ)) :
    ∃ hB : IsNuclearOperator (ratProjConvolutionOp hχ hN hα hs hj T hT hvT hv hX Φ),
      hilbertTrace ⟨_, hB⟩ = ∑' m : ℤ, dirichletConvEigenvalue χ (pr v) Φ m := by
  have h := dirichletFixedBox_convolution_trace_expansion hχ hN
    (T.image pr) (ratPrimes_spec T hT) (pr_prime v) hv (ratPrime_notMem_image hvT)
    (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs Φ
  obtain ⟨_h1, hN_Q, _h3, _h4, htr, _h6⟩ := h
  have hc := hilbertTrace_conj_equiv
    (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX) _ hN_Q
  exact ⟨hc.choose, hc.choose_spec.trans htr⟩

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 4, the positive bump through the project's dilation.** The transported convolution
operator of `dirichletPositiveBump` is `∫_{u ≥ 0} Φ₊(u) · ratProjSemigroup u du`, where
`ratProjSemigroup u` is the project's dilation by the norm section on classes of box tests
(`ratProjSemigroup_quotMap`); it is nuclear with trace zero. -/
theorem ratBridge_positiveBump (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    (∀ y, ratProjConvolutionOp hχ hN hα hs hj T hT hvT hv hX dirichletPositiveBump y =
      ∫ u : ℝ, if hu : 0 ≤ u then
        dirichletPositiveBump u • ratProjSemigroup hχ hN hα hs hj T hT hvT hv hX u hu y else 0) ∧
      ∃ hB : IsNuclearOperator (ratProjConvolutionOp hχ hN hα hs hj T hT hvT hv hX
        dirichletPositiveBump), hilbertTrace ⟨_, hB⟩ = 0 := by
  have h0 := dirichletFixedBox_traceNorm_lower_bound
  obtain ⟨c₀, _hc₀, hlow⟩ := h0
  have h := @hlow N _ χ hχ hN (T.image pr) (ratPrimes_spec T hT)
    (pr v) (pr_prime v) hv (ratPrime_notMem_image hvT) _ α s
    (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
  obtain ⟨hrep, _h2, hN_Q, _h4, htr, _h6, _h7⟩ := h
  refine ⟨fun y ↦ ?_, ?_⟩
  · change (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).symm
      (dirichletConvolutionOp hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v) hv
        (ratPrime_notMem_image hvT)
        (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
        dirichletPositiveBump
        (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX y)) = _
    rw [hrep, ← ContinuousLinearEquiv.integral_comp_comm]
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    by_cases hu : 0 ≤ u
    · simp only [hu, ↓reduceDIte, map_smul]
      rfl
    · simp only [hu, ↓reduceDIte, map_zero]
  · have hc := hilbertTrace_conj_equiv
      (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX) _ hN_Q
    exact ⟨hc.choose, hc.choose_spec.trans htr⟩

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 4, cardinal lifts by actual tests.** The cardinal lifts `f_m` of
`dirichletFixedBox_cardinal_lifts` (box `R(X)`, rows `δ_{nm}`, polynomial growth) are represented
by tests `g_m` of the absolute Paley–Wiener level `X` (same theta as `dirTest f_m`); the
quotient isomorphism sends the class of `g_m` to the rational class of `f_m`, and the classes of
the `g_m` in the completed project quotient grow polynomially in `|m|`. -/
theorem ratBridge_cardinal_lifts (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    ∃ (g : ℤ → primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X) (f : ℤ → 𝓢(ℝ, ℂ))
      (hmem : ∀ m, MemLp (dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ (f m))) 2
        (νR(α, s)))
      (hE : ∀ m, toDirichletStrip α s _ (hmem m) ∈
        dirichletStageSpace χ (T.image pr) Xr(X, T) α s hα hs),
      (∀ m, IsDirichletFixedBoxTest χ (ratDirichletBoxShift N X) (f m)) ∧
      (∀ m (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω (g m).val.val (k.val * ratNormSection t) =
        homogeneousAdelicTheta ω (dirTest hχ (f m)) (k.val * ratNormSection t)) ∧
      (∀ m, ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX
          ⟨ratProjQuotMap Sχ ω j T (insert v T) X (g m), ratProjQuotMap_mem _ _ _ _ _ _ (g m)⟩ =
        dirichletStageQuotMap hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v)
          (ratPrime_notMem_image hvT)
          (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
          ⟨toDirichletStrip α s _ (hmem m), hE m⟩) ∧
      (∀ m n, dirichletNormalizedRow χ (T.image pr) (pr v) Xr(X, T) α s hα hs n
        (toDirichletStrip α s _ (hmem m)) = if n = m then 1 else 0) ∧
      ∃ K : ℕ, ∃ C > (0 : ℝ), ∀ m,
        ‖ratProjQuotMap Sχ ω j T (insert v T) X (g m)‖ ≤ C * (1 + |(m : ℝ)|) ^ K := by
  have hprod := ratPrimes_prod_pos T
  have hR := ratDirichletBoxShift_pos hN hX
  have hdiv : (ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) / ∏ q ∈ T.image pr, (q : ℝ) =
      ratDirichletBoxShift N X := mul_div_cancel_right₀ _ hprod.ne'
  have hd := dirichletFixedBox_cardinal_lifts hχ hN (T.image pr) (ratPrimes_spec T hT)
    (pr_prime v) hv (ratPrime_notMem_image hvT) (mul_pos hR hprod) hα hs (α := α) (s := s)
  obtain ⟨f, hbox, hmem, hrow, K, C, hC, hbd⟩ := hd
  have hboxR (m : ℤ) : IsDirichletFixedBoxTest χ (ratDirichletBoxShift N X) (f m) := by
    have h := hbox m
    rw [hdiv] at h
    exact h
  choose g hg hgf using fun m ↦ ratBridge_dirichlet_isotypic_converse hχ hN hX (f m) (hboxR m).2
  have hE (m : ℤ) := mem_dirichletStageSpace_of_test (T.image pr) hα hs (hbox m) (hmem m)
  refine ⟨fun m ↦ ⟨g m, hg m⟩, f, hmem, hE, hboxR, hgf, fun m ↦ ?_, fun m n ↦ hrow m n (hmem m),
    K, massℝ * Real.sqrt massℝ * C,
    mul_pos (mul_pos ratMass_pos (Real.sqrt_pos.mpr ratMass_pos)) hC, fun m ↦ ?_⟩
  · exact ratBridge_dirichlet_quotient_iso_quotMap hχ hN hα hs hj T hT hvT hv hX ⟨g m, hg m⟩ (f m)
      (hgf m) (hmem m) (hE m)
  · have hcore := halfThetaMap_principalValue_of_mem hχ hN hj T hT (g m) (hg m) (f m) (hgf m)
      (hmem m)
    have h1 : ‖ratProjQuotMap Sχ ω j T (insert v T) X ⟨g m, hg m⟩‖ ≤
        ‖j (adelePolarPrincipalValue T (g m))‖ :=
      Submodule.norm_starProjection_apply_le _ _
    rw [hcore, map_smul, norm_smul, norm_ratStripEmbed, Complex.norm_real,
      Real.norm_of_nonneg ratMass_pos.le] at h1
    have h2 := hbd m (hmem m)
    have hc : 0 ≤ massℝ * Real.sqrt massℝ :=
      mul_nonneg ratMass_pos.le (Real.sqrt_nonneg _)
    calc ‖ratProjQuotMap Sχ ω j T (insert v T) X ⟨g m, hg m⟩‖
        ≤ massℝ * (Real.sqrt massℝ * ‖toDirichletStrip α s _ (hmem m)‖) := h1
      _ = massℝ * Real.sqrt massℝ * ‖toDirichletStrip α s _ (hmem m)‖ := by ring
      _ ≤ massℝ * Real.sqrt massℝ * (C * (1 + |(m : ℝ)|) ^ K) :=
          mul_le_mul_of_nonneg_left h2 hc
      _ = massℝ * Real.sqrt massℝ * C * (1 + |(m : ℝ)|) ^ K := by ring

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 4, the unconditional basis.** With the Hilbert basis `b` of `DirichletAvgQuotient`
from `dirichletFixedBox_unconditional_basis` (joint eigenvectors of the modulated action,
biorthogonal to the rows), the vectors `e_m = Φ⁻¹ (b m)` of the completed project quotient give an
unconditionally convergent expansion of every element, and their images under the quotient
isomorphism `Φ` keep the row properties. -/
theorem ratBridge_unconditional_basis (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    ∃ b : HilbertBasis ℤ ℂ (DirichletAvgQuotient χ hχ hN (T.image pr) (ratPrimes_spec T hT) (pr v)
        (pr_prime v) hv (ratPrime_notMem_image hvT) Xr(X, T) α s
        (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs),
      (∀ y : ratProjQuot Sχ ω j T (insert v T) X,
        HasSum (fun m ↦ b.repr ((dirichletAvgEquivQ χ hχ hN (T.image pr) (ratPrimes_spec T hT)
            (pr v) (pr_prime v) hv (ratPrime_notMem_image hvT) Xr(X, T) α s
            (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs).symm
              (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX y)) m •
          (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).symm (b m).val) y) ∧
      (∀ m : ℤ, dirichletQuotRow χ (T.image pr) (pr v) Xr(X, T) α s hα hs m
        (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX
          ((ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).symm (b m).val)) ≠ 0) ∧
      (∀ n m : ℤ, n ≠ m → dirichletQuotRow χ (T.image pr) (pr v) Xr(X, T) α s hα hs n
        (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX
          ((ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).symm (b m).val)) =
            0) := by
  have hd := dirichletFixedBox_unconditional_basis hχ hN (T.image pr) (ratPrimes_spec T hT)
    (pr_prime v) hv (ratPrime_notMem_image hvT)
    (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
  obtain ⟨b, _heig, _heigQ, _hproj, hrow, hrow0⟩ := hd
  set Φ := ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX
  set A := dirichletAvgEquivQ χ hχ hN (T.image pr) (ratPrimes_spec T hT) (pr v) (pr_prime v) hv
    (ratPrime_notMem_image hvT) Xr(X, T) α s
    (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
  refine ⟨b, fun y ↦ ?_, fun m ↦ ?_, fun n m hnm ↦ ?_⟩
  · have h := (b.hasSum_repr (A.symm (Φ y))).mapL (Φ.symm.toContinuousLinearMap.comp
      A.toContinuousLinearMap)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_smul,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] at h
    exact h
  · rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hrow m
  · rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hrow0 n m hnm

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 4, trace norm of the convolution operator.** On the completed project quotient the
trace norm of the transported convolution operator dominates `∑ ‖λ_m‖` (transferred from
`dirichletFixedBox_convolution_trace_expansion` by `traceNorm_conj_scaled`). -/
theorem ratBridge_convolution_traceNorm_ge (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (Φ : 𝓢(ℝ, ℂ)) (hB : IsNuclearOperator (ratProjConvolutionOp hχ hN hα hs hj T hT hvT hv hX Φ)) :
    ∑' m : ℤ, ‖dirichletConvEigenvalue χ (pr v) Φ m‖ ≤ traceNorm ⟨_, hB⟩ := by
  have hc : 0 < massℝ * Real.sqrt massℝ := mul_pos ratMass_pos (Real.sqrt_pos.mpr ratMass_pos)
  have h := dirichletFixedBox_convolution_trace_expansion hχ hN
    (T.image pr) (ratPrimes_spec T hT) (pr_prime v) hv (ratPrime_notMem_image hvT)
    (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs Φ
  obtain ⟨_h1, hN_Q, _h3, _h4, _htr, hle⟩ := h
  exact hle.trans_eq (traceNorm_conj_scaled
    (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX) _ hc
    (fun y ↦ norm_ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX y) _ hN_Q hB).symm

end Transfer


/-! ### The trace-norm lower bound on the project quotient -/

section LowerBound

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 4, the trace-norm lower bound on the project quotient.** There is a universal
`c₀ > 0` (that of `dirichletFixedBox_traceNorm_lower_bound`) such that for every primitive `χ`
mod `N > 1` and every stage, the convolution operator of `dirichletPositiveBump` transported to the
completed project quotient is `∫_{u ≥ 0} Φ₊(u) ratProjSemigroup u du` (the project's dilation), is
nuclear with trace `0`, and has trace norm at least `c₀ log p`. -/
theorem ratBridge_positiveBump_traceNorm_lower_bound :
    ∃ c₀ > (0 : ℝ), ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
      (hN : 1 < N) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)}
      (hj : IsRatHalfThetaMap (ratDirichletNormOneChar hχ) j)
      (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
      (hv : (pr v).Coprime N) {X : ℝ}
      (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X),
      (∀ y, ratProjConvolutionOp hχ hN hα hs hj T hT hvT hv hX dirichletPositiveBump y =
        ∫ u : ℝ, if hu : 0 ≤ u then
          dirichletPositiveBump u • ratProjSemigroup hχ hN hα hs hj T hT hvT hv hX u hu y
        else 0) ∧
      ∃ hB : IsNuclearOperator (ratProjConvolutionOp hχ hN hα hs hj T hT hvT hv hX
          dirichletPositiveBump),
        hilbertTrace ⟨_, hB⟩ = 0 ∧ c₀ * Real.log (pr v) ≤ traceNorm ⟨_, hB⟩ := by
  have h0 := dirichletFixedBox_traceNorm_lower_bound
  obtain ⟨c₀, hc₀, hlow⟩ := h0
  refine ⟨c₀, hc₀, ?_⟩
  intro N _ χ hχ hN α s hα hs j hj T hT v hvT hv X hX
  have hc : 0 < massℝ * Real.sqrt massℝ := mul_pos ratMass_pos (Real.sqrt_pos.mpr ratMass_pos)
  have hpb := ratBridge_positiveBump hχ hN hα hs hj T hT hvT hv hX
  have h := @hlow N _ χ hχ hN (T.image pr) (ratPrimes_spec T hT)
    (pr v) (pr_prime v) hv (ratPrime_notMem_image hvT) _ α s
    (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
  obtain ⟨_hrep, _h2, hN_Q, _h4, _htr, _h6, hlb⟩ := h
  refine ⟨hpb.1, hpb.2.choose, hpb.2.choose_spec, ?_⟩
  exact hlb.trans_eq (traceNorm_conj_scaled
    (ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX) _ hc
    (fun y ↦ norm_ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX y) _ hN_Q
    hpb.2.choose).symm

end LowerBound

/-! ### The setting of (11.3.1.3) over `ℚ` -/

section Setting

variable {N : ℕ} [NeZero N]

/-- Every ring endomorphism of `𝓞 ℚ ≅ ℤ` is the identity. -/
theorem ratRingOfIntegers_ringHom_apply (f : 𝓞 ℚ →+* 𝓞 ℚ) (x : 𝓞 ℚ) : f x = x := by
  have hx : x = (((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) x : ℤ) : 𝓞 ℚ) := by
    conv_lhs => rw [← (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm_apply_apply x]
    exact eq_intCast _ _
  rw [hx, map_intCast]

/-- Over `ℚ` a place lies over itself (for any algebra structure of `𝓞 ℚ` over itself). -/
theorem ratPlace_under_self {_ : Algebra (𝓞 ℚ) (𝓞 ℚ)} {_ : Algebra.IsIntegral (𝓞 ℚ) (𝓞 ℚ)}
    (w : Vℚ) : w.under (𝓞 ℚ) = w := by
  apply HeightOneSpectrum.ext
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap,
    ratRingOfIntegers_ringHom_apply]

/-- Over `ℚ` the places above a rational prime are that prime alone. -/
theorem ratPlacesAbove_eq (p : Vℚ) : (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset = {p} := by
  ext w
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton, ratPlace_under_self]

private theorem ratPrimaryDivisorial_infinite (S : Finset Vℚ) :
    (Set.ofPred (fun p : ℕ ↦ p.Prime ∧
      p ∉ S.image (fun v ↦ Rat.HeightOneSpectrum.natGenerator (v.under (𝓞 ℚ))))).Infinite := by
  have := Nat.infinite_setOfPred_prime.sdiff
    (S.image (fun v ↦ Rat.HeightOneSpectrum.natGenerator (v.under (𝓞 ℚ)))).finite_toSet
  refine this.mono ?_
  intro p hp
  exact ⟨hp.1, by simpa using hp.2⟩

theorem pr_primaryDivisorialPrime (S : Finset Vℚ) (k : ℕ) :
    pr (primaryDivisorialPrime S k) = Nat.nth (fun p ↦ p.Prime ∧
      p ∉ S.image (fun v ↦ Rat.HeightOneSpectrum.natGenerator (v.under (𝓞 ℚ)))) k :=
  pr_placeOf _ _

private theorem coprime_primaryDivisorialPrime (hN : 1 < N) (k : ℕ) :
    (pr (primaryDivisorialPrime (ratDirichletS N) k)).Coprime N := by
  rw [pr_primaryDivisorialPrime]
  have hmem := Nat.nth_mem_of_infinite (ratPrimaryDivisorial_infinite (ratDirichletS N)) k
  refine (Nat.Prime.coprime_iff_not_dvd hmem.1).mpr fun hdvd ↦ hmem.2 ?_
  refine Finset.mem_image.mpr ⟨placeOf _ hmem.1, ?_, ?_⟩
  · rw [mem_ratDirichletS (by omega), pr_placeOf]
    exact hdvd
  · rw [ratPlace_under_self]
    exact pr_placeOf _ _

open Classical in
private theorem mem_primaryDivisorialPlaces_rat (S : Finset Vℚ) (k : ℕ) (w : Vℚ) :
    w ∈ primaryDivisorialPlaces ℚ S k ↔ ∃ i < k, w = primaryDivisorialPrime S i := by
  unfold primaryDivisorialPlaces
  simp only [Finset.mem_biUnion, Finset.mem_range, ratPlacesAbove_eq, Finset.mem_singleton]

open Classical in
/-- Paper: §11.3.1.1, p. 493, and (11.3.1.3), p. 494, over `ℚ`. **The setting of stage 5.** For
`S = ratDirichletS N`, `T = primaryDivisorialPlaces ℚ S k` and `v = primaryDivisorialPrime S k`,
every place of `T` and `v` lie over primes coprime to `N`, `v ∉ T`, and the next packet set is
`insert v T`; so the results of this file (stated for `T` and `insert v T`) apply to the objects
of `primaryDivisorialAbsolutePW_quotient_bounds` verbatim. -/
theorem ratPrimaryDivisorial_setting (hN : 1 < N) (k : ℕ) :
    (∀ w ∈ primaryDivisorialPlaces ℚ (ratDirichletS N) k, (pr w).Coprime N) ∧
      primaryDivisorialPrime (ratDirichletS N) k ∉ primaryDivisorialPlaces ℚ (ratDirichletS N) k ∧
      (pr (primaryDivisorialPrime (ratDirichletS N) k)).Coprime N ∧
      primaryDivisorialPlaces ℚ (ratDirichletS N) (k + 1) =
        insert (primaryDivisorialPrime (ratDirichletS N) k)
          (primaryDivisorialPlaces ℚ (ratDirichletS N) k) := by
  refine ⟨fun w hw ↦ ?_, fun hk ↦ ?_, coprime_primaryDivisorialPrime hN k, ?_⟩
  · obtain ⟨i, -, rfl⟩ := (mem_primaryDivisorialPlaces_rat _ k w).mp hw
    exact coprime_primaryDivisorialPrime hN i
  · obtain ⟨i, hik, hi⟩ := (mem_primaryDivisorialPlaces_rat _ k _).mp hk
    have h := congrArg pr hi
    rw [pr_primaryDivisorialPrime, pr_primaryDivisorialPrime] at h
    exact hik.ne' (Nat.nth_injective (ratPrimaryDivisorial_infinite _) h)
  · rw [primaryDivisorialPlaces_succ, ratPlacesAbove_eq, Finset.union_comm, ← Finset.insert_eq]

end Setting

end RiemannMasullo.Isolated
