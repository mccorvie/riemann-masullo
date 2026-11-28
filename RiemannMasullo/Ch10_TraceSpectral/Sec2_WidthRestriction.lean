module
public import RiemannMasullo.Ch10_TraceSpectral.Sec2

/-! # Changing the width of the genuine theta quotient

At a fixed center and Sobolev degree the wider physical norm dominates the narrower
one. The representative-preserving map descends to a dense contraction of the true
theta quotients. Its kernel consists of wide classes approximable by genuine theta
sources in the narrow norm.
-/
@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal ENNReal NumberField.AdeleRing
namespace RiemannMasullo
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "x𝔽" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 x𝔽 (-α) α s
local notation "ν(" α ", " s ")" => intervalSobolevMeasure μ𝔽 x𝔽 (-α) α s

private theorem thetaWidth_density_le {α β : ℝ} (hα : 0 ≤ α) (h : α ≤ β) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x ≤ intervalSobolevDensity (-β) β s x := by
  unfold intervalSobolevDensity
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  rcases le_or_gt 0 x with hx | hx
  · apply (max_le _ _).trans (le_max_right _ _)
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα hx, mul_nonneg (sub_nonneg.mpr h) hx]
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr h) hx]
  · apply (max_le _ _).trans (le_max_left _ _)
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h) hx.le]
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx.le,
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h) hx.le]

private theorem thetaWidth_ambient {α β : ℝ} (hα : 0 ≤ α) (hab : α ≤ β) (s : ℝ) :
    ∃ I : W(β,s) →L[ℂ] W(α,s), DenseRange I ∧ ‖I‖ ≤ 1 ∧
      ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q := by
  have hle : ν(α,s) ≤ ν(β,s) :=
    withDensity_mono (.of_forall fun g ↦ ENNReal.ofReal_le_ofReal (thetaWidth_density_le hα hab s (x𝔽 g)))
  have h1 : ν(α,s) ≤ (1 : ℝ≥0∞) • ν(β,s) := by simpa using hle
  let U := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.one_ne_top h1
  have hU (q : W(β,s)) : (U q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q := Lp.coeFn_LpToLpOfMeasureLeSMul _ _ q
  let I : W(β,s) →L[ℂ] W(α,s) :=
    { toFun := U
      map_add' := U.map_add
      map_smul' := fun c q ↦ Lp.ext <| (hU (c • q)).trans <| Filter.EventuallyEq.trans (ae_mono hle (Lp.coeFn_smul c q)) <|
        ((hU q).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (U q)).symm
      cont := U.continuous }
  refine ⟨I, ?_, ?_, hU⟩
  · have hlog : Continuous x𝔽 := (NNReal.continuous_coe.comp (Units.continuous_val.comp
        (isProperMap_ideleClassNorm F).continuous)).log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    have hc (b : ℝ) : Continuous (fun g : C𝔽 ↦ intervalSobolevDensity (-b) b s (x𝔽 g)) := by
      unfold intervalSobolevDensity
      have hbase : Continuous (fun g : C𝔽 ↦ 1 + (x𝔽 g)^2) := continuous_const.add (hlog.pow 2)
      exact ((Real.continuous_exp.comp (continuous_const.mul hlog)).max
        (Real.continuous_exp.comp (continuous_const.mul hlog))).mul
          (hbase.rpow_const (p := s/2) (fun _ ↦ Or.inl (by dsimp; positivity)))
    let loc (b : ℝ) : IsLocallyFiniteMeasure (ν(b,s)) := IsLocallyFiniteMeasure.withDensity_ofReal (hc b)
    intro q
    apply EMetric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    obtain ⟨g, hg, hclose, hgc, _⟩ := (Lp.memLp q).exists_hasCompactSupport_eLpNorm_sub_le
      ENNReal.ofNat_ne_top hδ.ne'
    have hgν : MemLp g 2 (ν(β,s)) := hgc.memLp_of_hasCompactSupport hg
    have heq := (hU (hgν.toLp g)).trans (hle.absolutelyContinuous.ae_eq hgν.coeFn_toLp)
    refine ⟨I (hgν.toLp g), mem_range_self _, ?_⟩
    rw [Lp.edist_def]
    exact (eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub heq)).trans_le hclose |>.trans_lt hδε
  · rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ) I]
    change ‖U‖ ≤ 1
    simpa [U] using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) ENNReal.one_ne_top h1

local notation "Θ(" a ", " h ", " hs ")" => globalThetaSobolev F a (neg_le_self h) hs
local notation "Q(" a ", " h ", " hs ")" => spectralSobolevQuotient F a (neg_le_self h) hs

private theorem thetaWidth_theta_image (a : ℝ) {α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hs : 0 ≤ s) (I : W(β,s) →L[ℂ] W(α,s)) (hI : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q) :
    closure (I '' (Θ(a,hβ,hs) : Set _)) = (Θ(a,hα,hs) : Set _) := by
  let E (b : ℝ) (hb : 0 ≤ b) := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-b) b s
    (neg_le_self hb) hs).exists.choose
  have he (q : GlobalPolarFreeThetaSpace F) : I (E β hβ q) = E α hα q := by
    obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
    apply Lp.ext
    apply (hI _).trans
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    exact ((existsUnique_globalThetaSobolevEmbedding (F := F) a (-β) β s (neg_le_self hβ) hs).exists.choose_spec.2 f).trans
      ((existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (neg_le_self hα) hs).exists.choose_spec.2 f).symm
  have hmap : MapsTo I (range (E β hβ)) (range (E α hα)) :=
    fun _ ⟨v,hv⟩ ↦ ⟨v, hv ▸ (he v).symm⟩
  change closure (I '' closure (range (E β hβ))) = closure (range (E α hα))
  apply le_antisymm
  · exact closure_minimal (hmap.closure I.continuous).image_subset isClosed_closure
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨v, rfl⟩
    exact subset_closure ⟨E β hβ v, subset_closure (mem_range_self _), he v⟩

/-- Paper: Theorem 10.2.2.1, pp. 445–446. Restricting physical representatives to a
narrower weighted norm induces a dense contraction of the genuine theta quotients.
The image of the wide theta space is dense in the narrow theta space. A wide class
is lost precisely when its representative lies in that narrow closure. -/
theorem exists_spectralSobolevQuotient_widthRestriction (a : ℝ) {α β s : ℝ}
    (hα : 0 ≤ α) (hab : α ≤ β) (hs : 0 ≤ s) :
    let hβ := hα.trans hab
    ∃ (I : W(β,s) →L[ℂ] W(α,s)) (J : Q(a,hβ,hs) →L[ℂ] Q(a,hα,hs)),
      (∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q) ∧ DenseRange I ∧ ‖I‖ ≤ 1 ∧
      closure (I '' (Θ(a,hβ,hs) : Set _)) = (Θ(a,hα,hs) : Set _) ∧
      DenseRange J ∧ ‖J‖ ≤ 1 ∧
      (∀ q, J ((Θ(a,hβ,hs)).mkQ q) = (Θ(a,hα,hs)).mkQ (I q)) ∧
      ∀ q, (Θ(a,hβ,hs)).mkQ q ∈ J.ker ↔ I q ∈ Θ(a,hα,hs) := by
  intro hβ
  obtain ⟨I, hd, hi, hrep⟩ := thetaWidth_ambient (F := F) hα hab s
  let N := Θ(a,hα,hs)
  let M := Θ(a,hβ,hs)
  have hcl := thetaWidth_theta_image a hα hβ hs I hrep
  have hMN : M ≤ (N.mkQL.comp I).ker := by
    intro u hu
    change N.mkQ (I u) = 0
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change I u ∈ (Θ(a,hα,hs) : Set _)
    rw [← hcl]
    exact subset_closure (mem_image_of_mem I hu)
  let J := M.liftQL (N.mkQL.comp I) hMN
  have hJ (q : W(β,s)) : J (M.mkQ q) = N.mkQ (I q) := rfl
  refine ⟨I, J, hrep, hd, hi, hcl, ?_, ?_, hJ, fun q ↦ ?_⟩
  · have hsur : DenseRange N.mkQL := N.mkQ_surjective.denseRange
    exact (hsur.comp hd N.mkQL.continuous).mono (by rintro _ ⟨q,rfl⟩; exact ⟨M.mkQ q, hJ q⟩)
  · apply J.opNorm_le_bound zero_le_one
    intro q
    rw [one_mul]
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨u, hu, huε⟩ := Submodule.Quotient.norm_mk_lt (S := M) q hε
    rw [← hu]
    exact ((Submodule.Quotient.norm_mk_le N (I u)).trans (by simpa using I.le_of_opNorm_le hi u)).trans_lt
      (hu ▸ huε)
  · change N.mkQ (I q) = 0 ↔ _
    exact Submodule.Quotient.mk_eq_zero N

set_option quotPrecheck false

local notation "C₁" => (ideleClassNorm F).ker
local notation "raw(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jet(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp (raw(χ,j))

private theorem thetaWidth_haar_ac (b s : ℝ) (dual : Bool) :
    μ𝔽 ≪ intervalSobolevMeasure μ𝔽 x𝔽 (-b) b s dual := by
  have hlog : Continuous x𝔽 := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hd : Continuous (intervalSobolevDensity (-b) b s) := by
    unfold intervalSobolevDensity
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const (p := s/2) (fun _ ↦ Or.inl (by dsimp; positivity)))
  have hp (g : C𝔽) : 0 < intervalSobolevDensity (-b) b s (x𝔽 g) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  cases dual
  · exact withDensity_absolutelyContinuous' (hd.comp hlog).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp g))
  · exact withDensity_absolutelyContinuous' (hd.comp hlog).measurable.inv.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (hp g)))

private theorem thetaWidth_shared_jet (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (I : W(β,s) →L[ℂ] W(α,s)) (hI : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q)
    (q : W(β,s)) (j : SpectralStripJetIndex χ a α s) (k : SpectralStripJetIndex χ a β s)
    (hjk : j.val = k.val) :
    spectralSobolevPairing (I q) (jet(χ,hα,hs,j)) = spectralSobolevPairing q (jet(χ,hβ,hs,k)) := by
  have hv : raw(χ,j) = raw(χ,k) := by rw [hjk]
  apply integral_congr_ae
  filter_upwards [(thetaWidth_haar_ac α s false).ae_eq (hI q),
    (thetaWidth_haar_ac α s true).ae_eq (spectralStripJet_memLp χ hα hs j).coeFn_toLp,
    (thetaWidth_haar_ac β s true).ae_eq (spectralStripJet_memLp χ hβ hs k).coeFn_toLp] with g hg hj hk
  exact congrArg₂ (· * ·) hg (hj.trans ((congrFun hv g).trans hk.symm))

private theorem thetaWidth_narrow_index (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α β s : ℝ} (hα : 0 ≤ α) (hab : α < β) (j : SpectralStripJetIndex χ a α s) :
    ∃ k : SpectralStripJetIndex χ a β s, k.val = j.val := by
  obtain ⟨hjlo, hjhi⟩ := (j.mem_strip_order_pos hα).1
  refine ⟨⟨j.val, ?_⟩, rfl⟩
  rw [spectralStripMultiplicity_interior (show j.val.2.1 ∈ Ioo (-β) β by constructor <;> linarith)]
  have hc := j.property
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity at hc
  split_ifs at hc <;> first | exact hc | exact hc.trans_le (min_le_left _ _) | omega

/-- Paper: Theorem 10.2.2.1, p. 446. A genuine restriction between strictly nested
strip quotients is injective exactly when the narrower strip retains every wide zero
jet, including its derivative order. An individual missing jet already produces a
nonzero wide class that becomes approximable by theta sources in the narrow norm. -/
theorem spectralSobolevQuotient_widthRestriction_injective_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (a : ℝ) {α β s : ℝ} (hα : 0 ≤ α) (hab : α < β) (hs : 0 ≤ s)
    (I : W(β,s) →L[ℂ] W(α,s)) (hI : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q)
    (J : Q(a,(hα.trans hab.le),hs) →L[ℂ] Q(a,hα,hs))
    (hJ : ∀ q, J ((Θ(a,(hα.trans hab.le),hs)).mkQ q) = (Θ(a,hα,hs)).mkQ (I q)) :
    Injective J ↔ ∀ k : SpectralStripJetIndex χ a β s,
      ∃ j : SpectralStripJetIndex χ a α s, j.val = k.val := by
  classical
  let hβ := hα.trans hab.le
  let M := Θ(a,hβ,hs)
  let N := Θ(a,hα,hs)
  constructor
  · intro hJinj k
    by_contra hlost
    obtain ⟨q, hq⟩ := spectralStripJet_singleInterpolant χ hχ hβ hs k
    have hn : I q ∈ N := (spectralStripJet_commonKernel χ hχ hα hs (I q)).mpr fun j ↦ by
      obtain ⟨l, hl⟩ := thetaWidth_narrow_index χ hα hab j
      have hlk : l ≠ k := fun he ↦ hlost ⟨j, he ▸ hl.symm⟩
      exact (thetaWidth_shared_jet χ hα hβ hs I hI q j l hl.symm).trans ((hq l).trans (ite_eq_right hlk))
    have hw : q ∈ M := (Submodule.Quotient.mk_eq_zero M).mp <|
      hJinj ((hJ q).trans (((Submodule.Quotient.mk_eq_zero N).mpr hn).trans J.map_zero.symm))
    have hzero := (spectralStripJet_commonKernel χ hχ hβ hs q).mp hw k
    exact zero_ne_one ((hzero.symm.trans (hq k)).trans (ite_eq_left rfl))
  · intro hkeep
    suffices hk : J.ker = ⊥ from LinearMap.ker_eq_bot.mp hk
    apply bot_unique
    rintro x hx
    obtain ⟨q,rfl⟩ := M.mkQ_surjective x
    have hzero : J (M.mkQ q) = 0 := hx
    have hn : I q ∈ N := (Submodule.Quotient.mk_eq_zero N).mp ((hJ q).symm.trans hzero)
    apply (Submodule.Quotient.mk_eq_zero M).mpr
    apply (spectralStripJet_commonKernel χ hχ hβ hs q).mpr
    intro k
    obtain ⟨j, hj⟩ := hkeep k
    exact (thetaWidth_shared_jet χ hα hβ hs I hI q j k hj).symm.trans
      ((spectralStripJet_commonKernel χ hχ hα hs (I q)).mp hn j)

end RiemannMasullo
