module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CoshDefect_Isolated
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-!
# Spectral projections, iterated Neumann word recursion, and radial partition (`#7406`)

1. `coshIsometricSection`, `coshSpectralProjection_add_geometric`, norm bounds `≤ 1`,
   `coshSpectralProjection_comp_testAction_comp_section`, and `traceNorm_comp_hasSum_le`.
2. `wordProd`, `wordTest`, `wordDerivMajorant`, `wordDerivSum`, strong induction on derivative
   order for `summable_wordDerivSum`.
3. `traceNorm_coshGeometric_le_of_word_bound`: depth-`L → ∞` iterated Neumann recursion
   eliminating the geometric remainder (`S₀ ≤ 1 / 2`).
4. `exists_radial_partition_bruhat` and `traceNorm_coshGeometric_translate_le`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set Topology
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated.CoshPositiveWidth

section ProjectionsAndTraceNorm

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => logIdeleClassNorm F

/-- Isometric section `coshSpectralQuotient F a hα hs →L[ℂ] CoshIntervalSobolev F α s`
landing in the orthogonal complement `(coshGlobalThetaSobolev F a hα hs)ᗮ`. -/
def coshIsometricSection (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    coshSpectralQuotient F a hα hs →L[ℂ] CoshIntervalSobolev F α s :=
  let Θ := coshGlobalThetaSobolev (F := F) a hα hs
  let eQ := (coshSpectralQuotientToQuot (F := F) a hα hs).toContinuousLinearEquiv
  (Θ.orthogonal.subtypeL).comp
    (Θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap.comp
      eQ.toContinuousLinearMap)

lemma coshSpectralProjection_add_geometric (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    coshGeometricProjection (F := F) a hα hs + coshSpectralProjection (F := F) a hα hs =
      ContinuousLinearMap.id ℂ (CoshIntervalSobolev F α s) := by
  ext1 u
  exact (coshGlobalThetaSobolev (F := F) a hα hs).starProjection_add_starProjection_orthogonal u

lemma norm_coshGeometricProjection_le_one (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ‖coshGeometricProjection (F := F) a hα hs‖ ≤ 1 :=
  (coshGlobalThetaSobolev (F := F) a hα hs).starProjection_norm_le

lemma norm_coshSpectralProjection_le_one (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ‖coshSpectralProjection (F := F) a hα hs‖ ≤ 1 :=
  (coshGlobalThetaSobolev (F := F) a hα hs).orthogonal.starProjection_norm_le

lemma norm_coshIsometricSection_apply (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (q : coshSpectralQuotient F a hα hs) :
    ‖coshIsometricSection (F := F) a hα hs q‖ = ‖q‖ := by
  dsimp only [coshIsometricSection, ContinuousLinearMap.comp_apply,
    Submodule.coe_subtypeL, Submodule.coe_subtype, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact ((coshGlobalThetaSobolev (F := F) a hα hs).quotientEquivOrthogonal.norm_map _).trans
    ((coshSpectralQuotientToQuot (F := F) a hα hs).norm_map q)

lemma norm_coshIsometricSection_le_one (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ‖coshIsometricSection (F := F) a hα hs‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q ↦
    (norm_coshIsometricSection_apply a hα hs q).le.trans_eq (one_mul _).symm

lemma coshIsometricSection_comp_quotMk (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (coshIsometricSection (F := F) a hα hs).comp (coshQuotMk (F := F) a hα hs) =
      coshSpectralProjection (F := F) a hα hs := by
  let Θ := coshGlobalThetaSobolev (F := F) a hα hs
  ext1 u
  dsimp only [ContinuousLinearMap.comp_apply, coshIsometricSection, coshQuotMk,
    coshSpectralProjection, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [Submodule.coe_subtypeL, Submodule.coe_subtype,
    LinearIsometryEquiv.apply_symm_apply]
  have hzero : Θ.mkQ (Θ.starProjection u) = 0 :=
    (Submodule.Quotient.mk_eq_zero Θ).mpr (Θ.starProjection_apply_mem u)
  have hsame : Θ.mkQ u = Θ.mkQ (Θ.orthogonal.starProjection u) := by
    have hsplit := Θ.starProjection_add_starProjection_orthogonal u
    calc Θ.mkQ u = Θ.mkQ (Θ.starProjection u + Θ.orthogonal.starProjection u) := by rw [hsplit]
      _ = Θ.mkQ (Θ.starProjection u) + Θ.mkQ (Θ.orthogonal.starProjection u) := map_add _ _ _
      _ = Θ.mkQ (Θ.orthogonal.starProjection u) := by rw [hzero, zero_add]
  have hrep := Θ.quotientEquivOrthogonal_mk (Θ.orthogonal.starProjection u)
    (Θ.orthogonal.starProjection_apply_mem u)
  exact (congrArg (fun q ↦ (Θ.quotientEquivOrthogonal q).val) hsame).trans
    (congrArg Subtype.val hrep)

lemma coshQuotMk_comp_isometricSection (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (coshQuotMk (F := F) a hα hs).comp (coshIsometricSection (F := F) a hα hs) =
      ContinuousLinearMap.id ℂ (coshSpectralQuotient F a hα hs) := by
  let Θ := coshGlobalThetaSobolev (F := F) a hα hs
  let eQ := coshSpectralQuotientToQuot (F := F) a hα hs
  ext1 q
  obtain ⟨u, rfl⟩ := coshQuotMk_surjective a hα hs q
  have h1 : coshIsometricSection a hα hs (coshQuotMk a hα hs u) = coshSpectralProjection a hα hs u :=
    DFunLike.congr_fun (coshIsometricSection_comp_quotMk a hα hs) u
  dsimp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [h1]
  have hdiff : u - coshSpectralProjection a hα hs u = coshGeometricProjection a hα hs u :=
    sub_eq_of_eq_add (Θ.starProjection_add_starProjection_orthogonal u).symm
  have hq : Θ.mkQ (coshSpectralProjection a hα hs u) = Θ.mkQ u := by
    symm
    exact (Submodule.Quotient.eq Θ).mpr (by rw [hdiff]; exact Θ.starProjection_apply_mem u)
  dsimp only [coshQuotMk, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact congrArg eQ.symm hq

lemma norm_coshQuotMk_le_one (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ‖coshQuotMk (F := F) a hα hs‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ ?_
  rw [one_mul, ← norm_coshIsometricSection_apply a hα hs (coshQuotMk a hα hs u),
    show coshIsometricSection a hα hs (coshQuotMk a hα hs u) = coshSpectralProjection a hα hs u from
      DFunLike.congr_fun (coshIsometricSection_comp_quotMk a hα hs) u]
  exact (coshGlobalThetaSobolev (F := F) a hα hs).orthogonal.norm_starProjection_apply_le u

lemma coshSpectralProjection_comp_isometricSection (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (coshSpectralProjection (F := F) a hα hs).comp (coshIsometricSection (F := F) a hα hs) =
      coshIsometricSection (F := F) a hα hs := by
  rw [← coshIsometricSection_comp_quotMk (F := F) a hα hs, ContinuousLinearMap.comp_assoc,
    coshQuotMk_comp_isometricSection, ContinuousLinearMap.comp_id]

lemma coshGeometricProjection_comp_isometricSection (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (coshGeometricProjection (F := F) a hα hs).comp (coshIsometricSection (F := F) a hα hs) = 0 := by
  have hadd : (coshGeometricProjection (F := F) a hα hs + coshSpectralProjection (F := F) a hα hs).comp
      (coshIsometricSection (F := F) a hα hs) = coshIsometricSection (F := F) a hα hs := by
    rw [coshSpectralProjection_add_geometric, ContinuousLinearMap.id_comp]
  rw [ContinuousLinearMap.add_comp, coshSpectralProjection_comp_isometricSection] at hadd
  exact add_eq_right.mp hadd

lemma coshSpectralProjection_comp_testAction_comp_section (a : ℝ) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    (coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ) =
      (coshIsometricSection (F := F) a hα hs).comp
        ((coshSpectralConvolution a hα hs φ).comp (coshQuotMk a hα hs)) := by
  rw [← coshIsometricSection_comp_quotMk (F := F) a hα hs]
  ext1 u
  dsimp only [ContinuousLinearMap.comp_apply]
  exact congrArg (coshIsometricSection a hα hs) (coshSpectralConvolution_apply_mk a hα hs φ u).symm

lemma traceNorm_comp_hasSum_le {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (S : ι → nuclearEndomorphisms H) (T : H →L[ℂ] H)
    (hs : HasSum (fun i ↦ (S i).val) T) (c : ι → ℝ) (hc : Summable c)
    (hb : ∀ i, traceNorm (S i) ≤ c i) :
    ∃ h : IsNuclearOperator (A.comp T), traceNorm ⟨A.comp T, h⟩ ≤ ‖A‖ * ∑' i, c i := by
  let AS (i : ι) : nuclearEndomorphisms H := ⟨A.comp (S i).val, mul_mem_nuclearEndomorphisms_left A (S i)⟩
  have hs' : HasSum (fun i ↦ (AS i).val) (A.comp T) :=
    (ContinuousLinearMap.compL ℂ H H H A).hasSum hs
  have hle (i : ι) : traceNorm (AS i) ≤ ‖A‖ * c i :=
    (traceNorm_mul_left_le A (S i)).trans (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
  obtain ⟨h, htr⟩ := traceNorm_le_of_hasSum AS (A.comp T) hs' (fun i ↦ ‖A‖ * c i)
    (hc.mul_left ‖A‖) hle
  exact ⟨h, htr.trans_eq tsum_mul_left⟩

end ProjectionsAndTraceNorm

section WordExpansion

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F

/-- Product/sum bijection splitting index `0` from `Fin.tail` on `Fin (m + 1) → β`. -/
def finSuccEquiv (β : Type*) (m : ℕ) : β × (Fin m → β) ≃ (Fin (m + 1) → β) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, Fin.tail w)
  left_inv p := by rcases p with ⟨x, w⟩; ext1 <;> simp
  right_inv w := Fin.cons_self_tail w

/-- Equiv identifying `β` with constant functions `Fin 1 → β`. -/
def finOneEquiv (β : Type*) : β ≃ (Fin 1 → β) where
  toFun x _ := x
  invFun w := w 0
  left_inv _ := rfl
  right_inv w := funext fun i ↦ by rw [Fin.fin_one_eq_zero i]

/-- Product of the time defect factors along a word `w : Fin m → CoshDefectIndex`. -/
def wordProd (α s : ℝ) {m : ℕ} (w : Fin m → CoshDefectIndex) (t : ℝ) : ℂ :=
  ∏ i : Fin m, coshDefectT α s (w i) t

@[simp]
lemma wordProd_zero (α s : ℝ) (w : Fin 0 → CoshDefectIndex) (t : ℝ) : wordProd α s w t = 1 :=
  Fin.prod_univ_zero _

lemma wordProd_succ (α s : ℝ) {m : ℕ} (w : Fin (m + 1) → CoshDefectIndex) (t : ℝ) :
    wordProd α s w t = coshDefectT α s (w 0) t * wordProd α s (Fin.tail w) t :=
  Fin.prod_univ_succ _

lemma contDiff_wordProd (α s : ℝ) {m : ℕ} (w : Fin m → CoshDefectIndex) :
    ContDiff ℝ (⊤ : ℕ∞) (wordProd α s w) := by
  induction m with
  | zero =>
      have heq : wordProd α s w = fun _ ↦ (1 : ℂ) := funext fun t ↦ wordProd_zero α s w t
      rw [heq]; exact contDiff_const
  | succ m ih =>
      have heq : wordProd α s w = (coshDefectT α s (w 0)) * (wordProd α s (Fin.tail w)) :=
        funext fun t ↦ wordProd_succ α s w t
      rw [heq]
      exact (contDiff_coshDefectT α s (w 0)).mul (ih (Fin.tail w))

/-- Bruhat compactly supported test obtained by multiplying `φ` by `wordProd α s w (logNorm ·)`. -/
def wordTest (α s : ℝ) {m : ℕ} (w : Fin m → CoshDefectIndex) (φ : BruhatCompactSupport C𝔽) :
    BruhatCompactSupport C𝔽 :=
  radialMul (wordProd α s w) (contDiff_wordProd α s w) φ

lemma wordTest_zero (α s : ℝ) (w : Fin 0 → CoshDefectIndex) (φ : BruhatCompactSupport C𝔽) :
    wordTest α s w φ = φ := by
  refine Subtype.ext (funext fun g ↦ ?_)
  simp [wordTest, radialMul_apply]

lemma wordTest_radialMul (α s : ℝ) (ι : CoshDefectIndex) {m : ℕ} (w : Fin m → CoshDefectIndex)
    (φ : BruhatCompactSupport C𝔽) :
    wordTest α s w (radialMul (coshDefectT α s ι) (contDiff_coshDefectT α s ι) φ) =
      wordTest α s (Fin.cons ι w) φ := by
  refine Subtype.ext (funext fun g ↦ ?_)
  simp only [wordTest, radialMul_apply]
  rw [wordProd_succ, Fin.cons_zero, Fin.tail_cons]
  ring

lemma tsupport_wordTest_subset (α s : ℝ) {m : ℕ} (w : Fin m → CoshDefectIndex)
    (φ : BruhatCompactSupport C𝔽) :
    tsupport (wordTest α s w φ).val ⊆ tsupport φ.val :=
  tsupport_radialMul_subset _ _ _

/-- Pointwise bound on `iteratedDeriv r (wordProd α s w)` over `|t| ≤ δ`. -/
def wordDerivMajorant (α s δ : ℝ) : ℕ → (m : ℕ) → (Fin m → CoshDefectIndex) → ℝ
  | r, 0, _ => if r = 0 then 1 else 0
  | r, m + 1, w => ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) *
      coshDefectDerivBound α s δ q (w 0) * wordDerivMajorant α s δ (r - q) m (Fin.tail w)

@[simp]
lemma wordDerivMajorant_zero_word (α s δ : ℝ) (r : ℕ) (w : Fin 0 → CoshDefectIndex) :
    wordDerivMajorant α s δ r 0 w = if r = 0 then 1 else 0 := rfl

lemma wordDerivMajorant_succ (α s δ : ℝ) (r m : ℕ) (w : Fin (m + 1) → CoshDefectIndex) :
    wordDerivMajorant α s δ r (m + 1) w = ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) *
      coshDefectDerivBound α s δ q (w 0) * wordDerivMajorant α s δ (r - q) m (Fin.tail w) := rfl

lemma wordDerivMajorant_zero_deriv (α s δ : ℝ) (m : ℕ) (w : Fin m → CoshDefectIndex) :
    wordDerivMajorant α s δ 0 m w = ∏ i : Fin m, coshDefectDerivBound α s δ 0 (w i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [wordDerivMajorant_succ, Finset.range_one, Finset.sum_singleton, Nat.choose_self,
        Nat.cast_one, one_mul, Nat.sub_zero, ih, Fin.prod_univ_succ]
      rfl

lemma wordDerivMajorant_nonneg {α s δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ) (r m : ℕ)
    (w : Fin m → CoshDefectIndex) :
    0 ≤ wordDerivMajorant α s δ r m w := by
  induction m generalizing r with
  | zero => dsimp only [wordDerivMajorant]; split_ifs <;> norm_num
  | succ m ih =>
      rw [wordDerivMajorant_succ]
      exact Finset.sum_nonneg fun q _ ↦ mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (coshDefectDerivBound_nonneg hα hδ q _)) (ih (r - q) _)

lemma norm_iteratedDeriv_wordProd_le {α s δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ) (r m : ℕ)
    (w : Fin m → CoshDefectIndex) {t : ℝ} (ht : |t| ≤ δ) :
    ‖iteratedDeriv r (wordProd α s w) t‖ ≤ wordDerivMajorant α s δ r m w := by
  induction m generalizing r with
  | zero =>
      have heq : wordProd α s w = fun _ ↦ (1 : ℂ) := funext fun _ ↦ wordProd_zero α s w _
      rw [heq]
      rcases r with _ | r
      · simp
      · simp [iteratedDeriv_const]
  | succ m ih =>
      have heq : wordProd α s w = (coshDefectT α s (w 0)) * (wordProd α s (Fin.tail w)) :=
        funext fun x ↦ wordProd_succ α s w x
      rw [heq, iteratedDeriv_mul ((contDiff_coshDefectT α s (w 0)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
        ((contDiff_wordProd α s (Fin.tail w)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
        wordDerivMajorant_succ]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ ↦ ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, mul_assoc]
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul (norm_iteratedDeriv_coshDefectT_le (s := s) hα hδ q (w 0) ht)
          (ih (r - q) (Fin.tail w)) (norm_nonneg _)
          (coshDefectDerivBound_nonneg (s := s) hα hδ q (w 0)))
        (Nat.cast_nonneg (r.choose q))).trans_eq (mul_assoc _ _ _).symm

/-- Total sum `∑_{w : Fin m → CoshDefectIndex} wordDerivMajorant α s δ r m w`. -/
def wordDerivSum (α s δ : ℝ) : ℕ → ℕ → ℝ
  | r, 0 => if r = 0 then 1 else 0
  | r, m + 1 => ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) *
      (∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ q ι) * wordDerivSum α s δ (r - q) m

lemma wordDerivSum_nonneg {α s δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ) (r m : ℕ) :
    0 ≤ wordDerivSum α s δ r m := by
  induction m generalizing r with
  | zero => dsimp only [wordDerivSum]; split_ifs <;> norm_num
  | succ m ih =>
      dsimp only [wordDerivSum]
      exact Finset.sum_nonneg fun q _ ↦ mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (tsum_nonneg fun ι ↦ coshDefectDerivBound_nonneg hα hδ q ι))
        (ih (r - q))

lemma hasSum_wordDerivMajorant {α s δ : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 32) (r m : ℕ) :
    HasSum (wordDerivMajorant α s δ r m) (wordDerivSum α s δ r m) := by
  induction m generalizing r with
  | zero =>
      dsimp only [wordDerivSum]
      exact hasSum_unique _
  | succ m ih =>
      rw [← (finSuccEquiv CoshDefectIndex m).hasSum_iff]
      have hterm (q : ℕ) :
          HasSum (fun p : CoshDefectIndex × (Fin m → CoshDefectIndex) ↦
            (r.choose q : ℝ) * coshDefectDerivBound α s δ q p.1 *
              wordDerivMajorant α s δ (r - q) m p.2)
            ((r.choose q : ℝ) * (∑' ι, coshDefectDerivBound α s δ q ι) *
              wordDerivSum α s δ (r - q) m) := by
        have hq := (summable_coshDefectDerivBound hα hs hδ0 hδ1 q).hasSum
        have hih := ih (r - q)
        have hprod_nn : ∀ p : CoshDefectIndex × (Fin m → CoshDefectIndex),
            0 ≤ coshDefectDerivBound α s δ q p.1 * wordDerivMajorant α s δ (r - q) m p.2 :=
          fun p ↦ mul_nonneg (coshDefectDerivBound_nonneg hα hδ0 q p.1)
            (wordDerivMajorant_nonneg hα hδ0 (r - q) m p.2)
        have hprod_sum : Summable (fun p : CoshDefectIndex × (Fin m → CoshDefectIndex) ↦
            coshDefectDerivBound α s δ q p.1 * wordDerivMajorant α s δ (r - q) m p.2) := by
          refine (summable_prod_of_nonneg hprod_nn).mpr
            ⟨fun ι ↦ (hih.summable.mul_left _).congr fun _ ↦ rfl, ?_⟩
          have h_row (ι : CoshDefectIndex) :
              ∑' w, coshDefectDerivBound α s δ q ι * wordDerivMajorant α s δ (r - q) m w =
                coshDefectDerivBound α s δ q ι * wordDerivSum α s δ (r - q) m := by
            rw [tsum_mul_left, hih.tsum_eq]
          simp_rw [h_row]
          exact hq.summable.mul_right _
        simpa only [mul_assoc] using (hq.mul hih hprod_sum).mul_left (r.choose q : ℝ)
      refine (hasSum_sum fun q _ ↦ hterm q).congr_fun fun p ↦ ?_
      dsimp only [Function.comp_apply, finSuccEquiv, Equiv.coe_fn_mk]
      change _ = wordDerivMajorant α s δ r (m + 1) (Fin.cons p.1 p.2)
      rw [wordDerivMajorant_succ, Fin.cons_zero, Fin.tail_cons]

lemma summable_wordDerivMajorant {α s δ : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 32) (r m : ℕ) :
    Summable (wordDerivMajorant α s δ r m) :=
  (hasSum_wordDerivMajorant hα hs hδ0 hδ1 r m).summable

lemma wordDerivSum_zero (α s δ : ℝ) (m : ℕ) :
    wordDerivSum α s δ 0 m = (∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι) ^ m := by
  induction m with
  | zero => simp [wordDerivSum]
  | succ m ih =>
      rw [wordDerivSum, Finset.range_one, Finset.sum_singleton]
      simp [ih, pow_succ']

lemma summable_wordDerivSum {α s δ : ℝ} (hα : 0 ≤ α) (_hs : 0 ≤ s) (hδ0 : 0 ≤ δ)
    (_hδ1 : δ ≤ 1 / 32) (hS : ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι ≤ 1 / 2)
    (r : ℕ) :
    Summable (fun m ↦ wordDerivSum α s δ r m) := by
  let S₀ : ℝ := ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι
  have hS₀_nn : 0 ≤ S₀ := tsum_nonneg fun ι ↦ coshDefectDerivBound_nonneg hα hδ0 0 ι
  induction r using Nat.strong_induction_on with
  | ind r ih =>
      rcases r with _ | r
      · simp_rw [wordDerivSum_zero]
        exact summable_geometric_of_lt_one hS₀_nn (by linarith)
      · let inhom (m : ℕ) : ℝ := ∑ q ∈ Finset.range (r + 1),
            ((r + 1).choose (q + 1) : ℝ) *
              (∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ (q + 1) ι) *
              wordDerivSum α s δ (r + 1 - (q + 1)) m
        have h_inhom_sum : Summable inhom := by
          refine summable_sum fun q hq ↦ ?_
          have hsub : r + 1 - (q + 1) < r + 1 := by omega
          exact ((ih _ hsub).mul_left _).congr fun _ ↦ rfl
        have hstep (m : ℕ) : wordDerivSum α s δ (r + 1) (m + 1) =
            S₀ * wordDerivSum α s δ (r + 1) m + inhom m := by
          dsimp only [wordDerivSum, inhom]
          rw [Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
          rw [add_comm]
        have hinhom_nn (m : ℕ) : 0 ≤ inhom m := by
          refine Finset.sum_nonneg fun q _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_)
            (wordDerivSum_nonneg hα hδ0 _ m)
          exact tsum_nonneg fun ι ↦ coshDefectDerivBound_nonneg hα hδ0 _ ι
        have hpart (M : ℕ) :
            (1 - S₀) * ∑ m ∈ Finset.range M, wordDerivSum α s δ (r + 1) m ≤
              ∑ m ∈ Finset.range M, inhom m := by
          cases M with
          | zero => simp
          | succ M =>
              have hS_step : ∑ m ∈ Finset.range (M + 1), wordDerivSum α s δ (r + 1) m =
                  ∑ m ∈ Finset.range M, wordDerivSum α s δ (r + 1) (m + 1) := by
                rw [Finset.sum_range_succ',
                  show wordDerivSum α s δ (r + 1) 0 = 0 from by simp [wordDerivSum], add_zero]
              have hS_sub : (∑ m ∈ Finset.range (M + 1), wordDerivSum α s δ (r + 1) m) -
                  S₀ * ∑ m ∈ Finset.range M, wordDerivSum α s δ (r + 1) m =
                  ∑ m ∈ Finset.range M, inhom m := by
                rw [hS_step, Finset.mul_sum, ← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun m _ ↦ by linarith [hstep m]
              have hS_mul : S₀ * ∑ m ∈ Finset.range (M + 1), wordDerivSum α s δ (r + 1) m =
                  S₀ * ∑ m ∈ Finset.range M, wordDerivSum α s δ (r + 1) m +
                    S₀ * wordDerivSum α s δ (r + 1) M := by
                rw [Finset.sum_range_succ, mul_add]
              have hnn : 0 ≤ S₀ * wordDerivSum α s δ (r + 1) M :=
                mul_nonneg hS₀_nn (wordDerivSum_nonneg hα hδ0 _ M)
              rw [Finset.sum_range_succ (fun m ↦ inhom m) M]
              linarith [hS_sub, hS_mul, hnn, hinhom_nn M]
        refine summable_of_sum_range_le (fun m ↦ wordDerivSum_nonneg hα hδ0 _ m)
          (c := 2 * ∑' m, inhom m) fun M ↦ ?_
        have h1 : ∑ m ∈ Finset.range M, inhom m ≤ ∑' m, inhom m :=
          h_inhom_sum.sum_le_tsum (Finset.range M) fun m _ ↦ hinhom_nn m
        have hhalf : (1 / 2 : ℝ) * ∑ m ∈ Finset.range M, wordDerivSum α s δ (r + 1) m ≤
            (1 - S₀) * ∑ m ∈ Finset.range M, wordDerivSum α s δ (r + 1) m :=
          mul_le_mul_of_nonneg_right (by linarith)
            (Finset.sum_nonneg fun m _ ↦ wordDerivSum_nonneg hα hδ0 _ m)
        have h_res : ∑ m ∈ Finset.range M, wordDerivSum α s δ (r + 1) m ≤ 2 * ∑' m, inhom m := by
          have := hpart M
          linarith
        exact h_res

end WordExpansion

section RecursionTheorem

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => logIdeleClassNorm F

private lemma tsum_finSucc_eq {β : Type*} (m : ℕ) (f : (Fin (m + 1) → β) → ℝ)
    (hf : Summable f) (hrow : ∀ x, Summable fun w ↦ f (Fin.cons x w)) :
    (∑' x : β, ∑' w : Fin m → β, f (Fin.cons x w)) = ∑' v : Fin (m + 1) → β, f v := by
  have hp : Summable (fun p : β × (Fin m → β) ↦ f (Fin.cons p.1 p.2)) :=
    ((finSuccEquiv β m).summable_iff.mpr hf).congr fun _ ↦ rfl
  rw [← (finSuccEquiv β m).tsum_eq]
  exact (hp.tsum_prod' hrow).symm

private lemma tsum_finOne_eq {β : Type*} (g : (Fin 1 → β) → ℝ) :
    (∑' x : β, g (Fin.cons x Fin.elim0)) = ∑' v : Fin 1 → β, g v := by
  have heq : (fun x : β ↦ g (Fin.cons x Fin.elim0)) = fun x : β ↦ g (finOneEquiv β x) := by
    ext x
    congr 1
    ext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rw [heq]
  exact (finOneEquiv β).tsum_eq g

lemma traceNorm_coshGeometric_finite_depth (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (E : nuclearEndomorphisms (CoshIntervalSobolev F α s))
    (hE : (coshSpectralProjection (F := F) a hα hs).comp E.val = E.val)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 32) (L : ℕ) :
    ∀ (ψ : BruhatCompactSupport C𝔽),
      (∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ) →
      ∀ (B : (m : ℕ) → (Fin (m + 1) → CoshDefectIndex) → ℝ),
        (∀ m w, 0 ≤ B m w) →
        (∀ m, Summable (B m)) →
        (∀ m (w : Fin (m + 1) → CoshDefectIndex),
          traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp
            (coshTestAction hα hs (wordTest α s w ψ))).comp E.val,
            mul_mem_nuclearEndomorphisms_left
              ((coshSpectralProjection (F := F) a hα hs).comp
                (coshTestAction hα hs (wordTest α s w ψ))) E⟩ ≤ B m w) →
        traceNorm ⟨((coshGeometricProjection (F := F) a hα hs).comp
            (coshTestAction hα hs ψ)).comp E.val,
            mul_mem_nuclearEndomorphisms_left
              ((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ)) E⟩ ≤
          (∑ m ∈ Finset.range L, ∑' w : Fin (m + 1) → CoshDefectIndex, B m w) +
            (√(Real.exp (2 * α * δ) * (1 + δ) ^ s) * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) *
              traceNorm E * (∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι) ^ L := by
  let H := CoshIntervalSobolev F α s
  let P := coshSpectralProjection (F := F) a hα hs
  let G := coshGeometricProjection (F := F) a hα hs
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := traceNorm_normedSpaceCore (H := H)
  let C_d : ℝ := √(Real.exp (2 * α * δ) * (1 + δ) ^ s)
  have hC_d : 0 ≤ C_d := Real.sqrt_nonneg _
  let S₀ : ℝ := ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι
  have hS₀_nn : 0 ≤ S₀ := tsum_nonneg fun ι ↦ coshDefectDerivBound_nonneg hα hδ0 0 ι
  induction L with
  | zero =>
      intro ψ hsupp B _hB0 _hBsum _hBspec
      rw [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, mul_one]
      have htr := traceNorm_mul_left_le (G.comp (coshTestAction hα hs ψ)) E
      have hG : ‖G‖ ≤ 1 := norm_coshGeometricProjection_le_one a hα hs
      have hA : ‖coshTestAction (F := F) hα hs ψ‖ ≤ C_d * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽 :=
        coshTestAction_norm_le hα hs ψ hδ0 hsupp
      have hGA : ‖G.comp (coshTestAction hα hs ψ)‖ ≤ C_d * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽 :=
        (ContinuousLinearMap.opNorm_comp_le G (coshTestAction hα hs ψ)).trans
          ((mul_le_mul hG hA (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
      exact htr.trans (mul_le_mul_of_nonneg_right hGA (hcore.norm_nonneg E))
  | succ L ih =>
      intro ψ hsupp B hB0 hBsum hBspec
      let M (ι : CoshDefectIndex) : H →L[ℂ] H :=
        coshMulOp (coshDefectX α ι) (continuous_coshDefectX α ι).measurable
          (norm_coshDefectX_le_one α ι)
      let ψ_ι (ι : CoshDefectIndex) : BruhatCompactSupport C𝔽 :=
        radialMul (coshDefectT α s ι) (contDiff_coshDefectT α s ι) ψ
      have hsupp_ι (ι : CoshDefectIndex) : ∀ y, (ψ_ι ι).val y ≠ 0 → |logNorm y| ≤ δ := by
        intro y hy
        refine hsupp y fun h0 ↦ hy ?_
        simp [ψ_ι, radialMul_apply, h0]
      let B_ι (ι : CoshDefectIndex) (m : ℕ) (w : Fin (m + 1) → CoshDefectIndex) : ℝ :=
        B (m + 1) (Fin.cons ι w)
      have hB0_ι (ι : CoshDefectIndex) (m : ℕ) (w : Fin (m + 1) → CoshDefectIndex) :
          0 ≤ B_ι ι m w := hB0 (m + 1) (Fin.cons ι w)
      have hBsum_ι (ι : CoshDefectIndex) (m : ℕ) : Summable (B_ι ι m) :=
        ((finSuccEquiv CoshDefectIndex (m + 1)).summable_iff.mpr
          (hBsum (m + 1))).comp_injective (Prod.mk_right_injective ι)
      have hBspec_ι (ι : CoshDefectIndex) (m : ℕ) (w : Fin (m + 1) → CoshDefectIndex) :
          traceNorm ⟨(P.comp (coshTestAction hα hs (wordTest α s w (ψ_ι ι)))).comp E.val,
            mul_mem_nuclearEndomorphisms_left
              (P.comp (coshTestAction hα hs (wordTest α s w (ψ_ι ι)))) E⟩ ≤ B_ι ι m w := by
        dsimp only [P, B_ι]
        rw [wordTest_radialMul]
        exact hBspec (m + 1) (Fin.cons ι w)
      have h_ih (ι : CoshDefectIndex) :=
        ih (ψ_ι ι) (hsupp_ι ι) (B_ι ι) (hB0_ι ι) (hBsum_ι ι) (hBspec_ι ι)
      have h_int_ψ : Integrable (fun y : C𝔽 ↦ ‖ψ.val y‖) μ𝔽 :=
        (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)).norm.integrable_of_hasCompactSupport
          ψ.property.2.norm
      have h_int_ι (ι : CoshDefectIndex) :
          ∫ y : C𝔽, ‖(ψ_ι ι).val y‖ ∂μ𝔽 ≤ coshDefectDerivBound α s δ 0 ι * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽 := by
        rw [← integral_const_mul]
        refine integral_mono ?_ (h_int_ψ.const_mul _) fun y ↦ ?_
        · exact (continuous_of_bruhatSmooth
            ((mem_bruhatSmoothSubmodule_iff _).mp (ψ_ι ι).property.1)).norm.integrable_of_hasCompactSupport
            (ψ_ι ι).property.2.norm
        · dsimp only [ψ_ι, radialMul_apply]
          by_cases hy : ψ.val y = 0
          · simp [hy]
          · rw [norm_mul]
            have hT := norm_iteratedDeriv_coshDefectT_le (s := s) hα hδ0 0 ι (hsupp y hy)
            rw [iteratedDeriv_zero] at hT
            exact mul_le_mul_of_nonneg_right hT (norm_nonneg _)
      have h_hasSum_diff := hasSum_coshTestAction_sub_adjoint hα hs hδ0 hδ1 ψ hsupp
      let R_E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
        LinearMap.mkContinuous
          { toFun := fun T ↦ T.comp E.val
            map_add' := fun T₁ T₂ ↦ by ext1 v; simp
            map_smul' := fun c T ↦ by ext1 v; simp }
          ‖E.val‖ fun T ↦ (ContinuousLinearMap.opNorm_comp_le T E.val).trans_eq (mul_comm _ _)
      let S_term (ι : CoshDefectIndex) : nuclearEndomorphisms H :=
        ⟨((G.comp (M ι)).comp (coshTestAction hα hs (ψ_ι ι))).comp E.val,
          mul_mem_nuclearEndomorphisms_left
            ((G.comp (M ι)).comp (coshTestAction hα hs (ψ_ι ι))) E⟩
      have hS_hasSum : HasSum (fun ι ↦ (S_term ι).val)
          ((G.comp (coshTestAction hα hs ψ)).comp E.val) := by
        have h1 : HasSum
            (fun ι ↦ (G.comp ((M ι).comp (coshTestAction hα hs (ψ_ι ι)))).comp E.val)
            ((G.comp (coshTestAction hα hs ψ -
              (coshTestAction hα hs (bruhatAdjoint ψ)).adjoint)).comp E.val) :=
          R_E.hasSum ((ContinuousLinearMap.compL ℂ H H H G).hasSum h_hasSum_diff)
        have hzero_adj :
            (G.comp (coshTestAction hα hs (bruhatAdjoint ψ)).adjoint).comp E.val = 0 := by
          rw [← hE, ← ContinuousLinearMap.comp_assoc (G.comp _) P E.val,
            ContinuousLinearMap.comp_assoc G _ P,
            coshGeometricProjection_comp_adjoint_comp_spectral a hα hs (bruhatAdjoint ψ),
            ContinuousLinearMap.zero_comp]
        have htarget :
            (G.comp (coshTestAction hα hs ψ -
              (coshTestAction hα hs (bruhatAdjoint ψ)).adjoint)).comp E.val =
              (G.comp (coshTestAction hα hs ψ)).comp E.val := by
          rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, hzero_adj, sub_zero]
        rw [htarget] at h1
        exact h1.congr_fun fun ι ↦ by
          simp only [S_term, ContinuousLinearMap.comp_assoc]
      let c (ι : CoshDefectIndex) : ℝ :=
        B 0 (Fin.cons ι Fin.elim0) +
          (∑ m ∈ Finset.range L, ∑' w : Fin (m + 1) → CoshDefectIndex, B (m + 1) (Fin.cons ι w)) +
          C_d * (coshDefectDerivBound α s δ 0 ι * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) * traceNorm E * S₀ ^ L
      have hc_bound (ι : CoshDefectIndex) : traceNorm (S_term ι) ≤ c ι := by
        let Tspec : nuclearEndomorphisms H :=
          ⟨(P.comp (coshTestAction hα hs (ψ_ι ι))).comp E.val,
            mul_mem_nuclearEndomorphisms_left (P.comp (coshTestAction hα hs (ψ_ι ι))) E⟩
        let Tgeom : nuclearEndomorphisms H :=
          ⟨(G.comp (coshTestAction hα hs (ψ_ι ι))).comp E.val,
            mul_mem_nuclearEndomorphisms_left (G.comp (coshTestAction hα hs (ψ_ι ι))) E⟩
        have hsplit : (S_term ι).val = (G.comp (M ι)).comp (Tspec + Tgeom).val := by
          change ((G.comp (M ι)).comp (coshTestAction hα hs (ψ_ι ι))).comp E.val =
            (G.comp (M ι)).comp ((P.comp (coshTestAction hα hs (ψ_ι ι))).comp E.val +
              (G.comp (coshTestAction hα hs (ψ_ι ι))).comp E.val)
          rw [← ContinuousLinearMap.add_comp, ← ContinuousLinearMap.add_comp, add_comm P G,
            coshSpectralProjection_add_geometric, ContinuousLinearMap.id_comp,
            ContinuousLinearMap.comp_assoc]
        have h_spec_b : traceNorm Tspec ≤ B 0 (Fin.cons ι Fin.elim0) := by
          have h0 : wordTest α s (Fin.cons ι (Fin.elim0 : Fin 0 → CoshDefectIndex)) ψ = ψ_ι ι := by
            rw [← wordTest_radialMul, wordTest_zero]
          simpa only [h0] using hBspec 0 (Fin.cons ι Fin.elim0)
        have hGM : ‖G.comp (M ι)‖ ≤ 1 :=
          (ContinuousLinearMap.opNorm_comp_le G (M ι)).trans
            ((mul_le_mul (norm_coshGeometricProjection_le_one a hα hs)
              (norm_coshMulOp_le (coshDefectX α ι) (continuous_coshDefectX α ι).measurable
                zero_le_one (norm_coshDefectX_le_one α ι))
              (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
        have htr_le : traceNorm (S_term ι) ≤ ‖G.comp (M ι)‖ * (traceNorm Tspec + traceNorm Tgeom) := by
          have h_eq : S_term ι = ⟨(G.comp (M ι)) * (Tspec + Tgeom).val,
              mul_mem_nuclearEndomorphisms_left (G.comp (M ι)) (Tspec + Tgeom)⟩ :=
            Subtype.ext hsplit
          rw [h_eq]
          exact (traceNorm_mul_left_le (G.comp (M ι)) (Tspec + Tgeom)).trans
            (mul_le_mul_of_nonneg_left (hcore.norm_triangle Tspec Tgeom) (norm_nonneg _))
        have hgeom_le : traceNorm Tgeom ≤
            (∑ m ∈ Finset.range L, ∑' w : Fin (m + 1) → CoshDefectIndex, B (m + 1) (Fin.cons ι w)) +
              C_d * (coshDefectDerivBound α s δ 0 ι * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) *
                traceNorm E * S₀ ^ L :=
          (h_ih ι).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h_int_ι ι) hC_d)
              (hcore.norm_nonneg E))
            (pow_nonneg hS₀_nn L)))
        have h_rhs_nn : 0 ≤ traceNorm Tspec + traceNorm Tgeom :=
          add_nonneg (hcore.norm_nonneg Tspec) (hcore.norm_nonneg Tgeom)
        exact htr_le.trans (((mul_le_mul_of_nonneg_right hGM h_rhs_nn).trans_eq (one_mul _)).trans
          (by linarith))
      have h_b0_sum : Summable (fun ι : CoshDefectIndex ↦ B 0 (Fin.cons ι Fin.elim0)) :=
        ((finOneEquiv CoshDefectIndex).summable_iff.mpr (hBsum 0)).congr fun ι ↦
          congrArg (B 0) (funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl)
      have h_Bm_sum (m : ℕ) : Summable (fun ι : CoshDefectIndex ↦
          ∑' w : Fin (m + 1) → CoshDefectIndex, B (m + 1) (Fin.cons ι w)) := by
        have hp : Summable (fun p : CoshDefectIndex × (Fin (m + 1) → CoshDefectIndex) ↦
            B (m + 1) (Fin.cons p.1 p.2)) :=
          (finSuccEquiv CoshDefectIndex (m + 1)).summable_iff.mpr (hBsum (m + 1))
        exact (hp.hasSum.prod_fiberwise fun ι ↦ (hBsum_ι ι m).hasSum).summable
      have h_fin_sum : Summable (fun ι : CoshDefectIndex ↦
          ∑ m ∈ Finset.range L, ∑' w : Fin (m + 1) → CoshDefectIndex, B (m + 1) (Fin.cons ι w)) :=
        summable_sum fun m _ ↦ h_Bm_sum m
      have h_rem_sum : Summable (fun ι : CoshDefectIndex ↦
          C_d * (coshDefectDerivBound α s δ 0 ι * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) * traceNorm E * S₀ ^ L) := by
        have hb0 := summable_coshDefectDerivBound (s := s) hα hs hδ0 hδ1 0
        exact (((hb0.mul_right _).mul_left C_d).mul_right (traceNorm E)).mul_right (S₀ ^ L)
      have hc_sum : Summable c := (h_b0_sum.add h_fin_sum).add h_rem_sum
      obtain ⟨_hnuc, htr_total⟩ := traceNorm_le_of_hasSum S_term
        ((G.comp (coshTestAction hα hs ψ)).comp E.val) hS_hasSum c hc_sum hc_bound
      refine htr_total.trans_eq ?_
      dsimp only [c]
      rw [(h_b0_sum.add h_fin_sum).tsum_add h_rem_sum, h_b0_sum.tsum_add h_fin_sum,
        tsum_finOne_eq (B 0), (hasSum_sum fun m _ ↦ (h_Bm_sum m).hasSum).tsum_eq]
      have h_sw (m : ℕ) :
          (∑' ι : CoshDefectIndex, ∑' w : Fin (m + 1) → CoshDefectIndex, B (m + 1) (Fin.cons ι w)) =
            ∑' v : Fin (m + 2) → CoshDefectIndex, B (m + 1) v :=
        tsum_finSucc_eq (m + 1) (B (m + 1)) (hBsum (m + 1)) fun ι ↦ hBsum_ι ι m
      simp_rw [h_sw]
      have h_rem_eq :
          (∑' ι : CoshDefectIndex, C_d * (coshDefectDerivBound α s δ 0 ι * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) *
            traceNorm E * S₀ ^ L) =
            (C_d * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) * traceNorm E * S₀ ^ (L + 1) := by
        have heq : (fun ι : CoshDefectIndex ↦
            C_d * (coshDefectDerivBound α s δ 0 ι * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) * traceNorm E * S₀ ^ L) =
            fun ι ↦ coshDefectDerivBound α s δ 0 ι *
              ((C_d * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) * traceNorm E * S₀ ^ L) := by
          ext ι; ring
        rw [heq, tsum_mul_right, pow_succ' S₀ L]
        change S₀ * ((C_d * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) * traceNorm E * S₀ ^ L) = _
        ring
      dsimp only [C_d] at h_rem_eq
      have h_range_eq : (∑' v : Fin 1 → CoshDefectIndex, B 0 v) +
          ∑ m ∈ Finset.range L, ∑' v : Fin (m + 2) → CoshDefectIndex, B (m + 1) v =
          ∑ m ∈ Finset.range (L + 1), ∑' w : Fin (m + 1) → CoshDefectIndex, B m w := by
        rw [Finset.sum_range_succ' (fun m ↦ ∑' w : Fin (m + 1) → CoshDefectIndex, B m w) L, add_comm]
      rw [h_rem_eq, h_range_eq]

lemma traceNorm_coshGeometric_le_of_word_bound (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (E : nuclearEndomorphisms (CoshIntervalSobolev F α s))
    (hE : (coshSpectralProjection (F := F) a hα hs).comp E.val = E.val)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 32)
    (hS : ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι ≤ 1 / 2)
    (ψ : BruhatCompactSupport C𝔽) (hsupp : ∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ)
    (B : (m : ℕ) → (Fin (m + 1) → CoshDefectIndex) → ℝ)
    (hB0 : ∀ m w, 0 ≤ B m w) (hBsum : ∀ m, Summable (B m))
    (hB_total : Summable (fun m ↦ ∑' w : Fin (m + 1) → CoshDefectIndex, B m w))
    (hBspec : ∀ m (w : Fin (m + 1) → CoshDefectIndex),
      traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp
        (coshTestAction hα hs (wordTest α s w ψ))).comp E.val,
        mul_mem_nuclearEndomorphisms_left
          ((coshSpectralProjection (F := F) a hα hs).comp
            (coshTestAction hα hs (wordTest α s w ψ))) E⟩ ≤ B m w) :
    traceNorm ⟨((coshGeometricProjection (F := F) a hα hs).comp
        (coshTestAction hα hs ψ)).comp E.val,
        mul_mem_nuclearEndomorphisms_left
          ((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ)) E⟩ ≤
      ∑' m : ℕ, ∑' w : Fin (m + 1) → CoshDefectIndex, B m w := by
  let S₀ : ℝ := ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι
  have hS₀_nn : 0 ≤ S₀ := tsum_nonneg fun ι ↦ coshDefectDerivBound_nonneg hα hδ0 0 ι
  let C_rem : ℝ := (√(Real.exp (2 * α * δ) * (1 + δ) ^ s) * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) * traceNorm E
  have h_lim1 : Tendsto (fun L : ℕ ↦ ∑ m ∈ Finset.range L, ∑' w : Fin (m + 1) → CoshDefectIndex, B m w)
      atTop (𝓝 (∑' m : ℕ, ∑' w : Fin (m + 1) → CoshDefectIndex, B m w)) :=
    hB_total.hasSum.tendsto_sum_nat
  have h_lim2 : Tendsto (fun L : ℕ ↦ C_rem * S₀ ^ L) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hS₀_nn (by linarith)).const_mul C_rem
  have h_lim : Tendsto (fun L : ℕ ↦
      (∑ m ∈ Finset.range L, ∑' w : Fin (m + 1) → CoshDefectIndex, B m w) + C_rem * S₀ ^ L)
      atTop (𝓝 (∑' m : ℕ, ∑' w : Fin (m + 1) → CoshDefectIndex, B m w)) := by
    simpa only [add_zero] using h_lim1.add h_lim2
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim fun L ↦ ?_
  exact traceNorm_coshGeometric_finite_depth a hα hs E hE hδ0 hδ1 L ψ hsupp B hB0 hBsum hBspec

end RecursionTheorem

section RadialPartition

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => logIdeleClassNorm F

private lemma logNorm_normSection_logEquiv (t : ℝ) :
    logNorm (QuotientGroup.mk (canonicalIdeleNormSection F
      (positiveRealLogEquiv.symm (Multiplicative.ofAdd t)))) = t := by
  change Real.log ((ideleNorm F (canonicalIdeleNormSection F
    (positiveRealLogEquiv.symm (Multiplicative.ofAdd t)))).val : ℝ) = t
  rw [canonicalIdeleNormSection_rightInverse F]
  have h := positiveRealLogEquiv_apply (positiveRealLogEquiv.symm (Multiplicative.ofAdd t))
  rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
  exact h.symm

private lemma logNorm_mul_ker {k : (ideleClassNorm F).ker} {g : C𝔽} :
    logNorm (k.val⁻¹ * g) = logNorm g := by
  have hk : continuousIdeleClassNorm F k.val = 1 := k.property
  change Real.log ((continuousIdeleClassNorm F (k.val⁻¹ * g)).val : ℝ) =
    Real.log ((continuousIdeleClassNorm F g).val : ℝ)
  rw [map_mul, map_inv, hk, inv_one, one_mul]

/-- Smooth compactly supported radial partition of unity of `φ` into tests `ψ j` whose
log-norm supports lie inside `[-δ, δ]` after shifting by norm-section points `h j`. -/
lemma exists_radial_partition_bruhat (φ : BruhatCompactSupport C𝔽) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (M : ℕ) (h : Fin M → C𝔽) (ψ : Fin M → BruhatCompactSupport C𝔽),
      (∀ j y, (ψ j).val y ≠ 0 → |logNorm y| ≤ δ) ∧
      (φ = ∑ j : Fin M, bruhatLeftTranslate (h j) (ψ j)) ∧
      (∀ (k : (ideleClassNorm F).ker) (ω : ℂ), (∀ g : C𝔽, φ.val (k.val⁻¹ * g) = ω * φ.val g) →
        ∀ j g, (ψ j).val (k.val⁻¹ * g) = ω * (ψ j).val g) := by
  obtain ⟨R₀, hR₀⟩ := φ.property.2.exists_bound_of_continuousOn continuous_logNorm.continuousOn
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)
  have hR_supp (y : C𝔽) (hy : φ.val y ≠ 0) : |logNorm y| ≤ R := by
    have h := hR₀ y (subset_tsupport _ hy)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * (R + 1)) / δ)
  let M : ℕ := 2 * N + 1
  let c (j : Fin M) : ℝ := ((j.val : ℝ) - (N : ℝ)) * (δ / 2)
  let b (j : Fin M) : ContDiffBump (c j) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let b_cov : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR_pos, lt_add_one R⟩
  let denom (x : ℝ) : ℝ := (1 - b_cov x) + ∑ j : Fin M, b j x
  have h_cover (x : ℝ) (hx : |x| ≤ R + 1) : ∃ j : Fin M, |x - c j| ≤ δ / 2 := by
    have hN_mul : R + 1 < (N : ℝ) * (δ / 2) := by
      have h1 := mul_lt_mul_of_pos_right hN hδ
      rw [div_mul_cancel₀ _ hδ.ne'] at h1
      linarith
    have hdiv_lt : (R + 1) / (δ / 2) < (N : ℝ) := (div_lt_iff₀ (by positivity : 0 < δ / 2)).mpr hN_mul
    have hx1 : -(N : ℝ) ≤ x / (δ / 2) := by
      have hlo := (abs_le.mp hx).1
      have hdiv := div_le_div_of_nonneg_right hlo (by positivity : 0 ≤ δ / 2)
      rw [neg_div] at hdiv
      linarith
    have hx2 : x / (δ / 2) ≤ (N : ℝ) := by
      have hhi := (abs_le.mp hx).2
      have := div_le_div_of_nonneg_right hhi (by positivity : 0 ≤ δ / 2)
      linarith
    let u : ℝ := x / (δ / 2) + (N : ℝ) + 1 / 2
    have hu0 : 0 ≤ u := by dsimp only [u]; linarith
    have huM : u < (M : ℝ) := by
      dsimp only [u, M]
      push_cast
      linarith
    let k0 : ℕ := Nat.floor u
    have hk0_lt : k0 < M := (Nat.floor_lt hu0).mpr huM
    refine ⟨⟨k0, hk0_lt⟩, ?_⟩
    have hk1 : (k0 : ℝ) ≤ u := Nat.floor_le hu0
    have hk2 : u < (k0 : ℝ) + 1 := Nat.lt_floor_add_one u
    have hband : |x / (δ / 2) + (N : ℝ) - (k0 : ℝ)| ≤ 1 / 2 := by
      dsimp only [u] at hk1 hk2
      rw [abs_le]
      constructor <;> linarith
    have heq : x - c ⟨k0, hk0_lt⟩ = (x / (δ / 2) + (N : ℝ) - (k0 : ℝ)) * (δ / 2) := by
      dsimp only [c]
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < δ / 2)]
    exact (mul_le_mul_of_nonneg_right hband (by positivity : 0 ≤ δ / 2)).trans (by linarith)
  have hdenom_ge_one (x : ℝ) : 1 ≤ denom x := by
    have hcov_nn : 0 ≤ b_cov x := b_cov.nonneg' x
    have hcov_le : b_cov x ≤ 1 := b_cov.le_one
    have hsum_nn : 0 ≤ ∑ j : Fin M, b j x := Finset.sum_nonneg fun j _ ↦ (b j).nonneg' x
    by_cases hx : |x| ≤ R + 1
    · obtain ⟨j₀, hj₀⟩ := h_cover x hx
      have hb_one : b j₀ x = 1 :=
        (b j₀).one_of_mem_closedBall (by simpa [Real.dist_eq] using hj₀)
      have hj₀_le : b j₀ x ≤ ∑ j : Fin M, b j x :=
        Finset.single_le_sum (f := fun j ↦ b j x) (fun j _ ↦ (b j).nonneg' x) (Finset.mem_univ j₀)
      dsimp only [denom]
      linarith
    · have hx' : b_cov.rOut ≤ dist x 0 := by
        simp only [b_cov, Real.dist_eq, sub_zero]
        exact le_of_not_ge hx
      have hcov_zero : b_cov x = 0 := b_cov.zero_of_le_dist hx'
      dsimp only [denom]
      linarith
  have hdenom_cd : ContDiff ℝ (⊤ : ℕ∞) denom :=
    (contDiff_const.sub b_cov.contDiff).add (ContDiff.sum fun j _ ↦ (b j).contDiff)
  have hdenom_eq_sum {x : ℝ} (hx : |x| ≤ R) : denom x = ∑ j : Fin M, b j x := by
    have h1 : b_cov x = 1 := b_cov.one_of_mem_closedBall (by simpa [b_cov, Real.dist_eq] using hx)
    dsimp only [denom]
    rw [h1, sub_self, zero_add]
  let r (j : Fin M) (x : ℝ) : ℂ := ((b j x / denom x : ℝ) : ℂ)
  have hr_cd (j : Fin M) : ContDiff ℝ (⊤ : ℕ∞) (r j) :=
    Complex.ofRealCLM.contDiff.comp ((b j).contDiff.div hdenom_cd fun x ↦ (by linarith [hdenom_ge_one x]))
  let h (j : Fin M) : C𝔽 :=
    QuotientGroup.mk (canonicalIdeleNormSection F (positiveRealLogEquiv.symm (Multiplicative.ofAdd (c j))))
  let ψ (j : Fin M) : BruhatCompactSupport C𝔽 :=
    bruhatLeftTranslate (h j)⁻¹ (radialMul (r j) (hr_cd j) φ)
  refine ⟨M, h, ψ, ?_, ?_, ?_⟩
  · intro j y hy
    change (radialMul (r j) (hr_cd j) φ).val ((h j)⁻¹⁻¹ * y) ≠ 0 at hy
    rw [inv_inv, radialMul_apply] at hy
    have hr_ne : r j (logNorm (h j * y)) ≠ 0 := left_ne_zero_of_mul hy
    have hb_ne : b j (logNorm (h j * y)) ≠ 0 := by
      intro hb0
      exact hr_ne (by simp [r, hb0])
    have hmem : logNorm (h j * y) ∈ Function.support (b j) := hb_ne
    rw [(b j).support_eq] at hmem
    have hdist := Metric.mem_ball.mp hmem
    rw [Real.dist_eq] at hdist
    have hlog : logNorm (h j * y) = c j + logNorm y := by
      change Real.log ((continuousIdeleClassNorm F (h j * y)).val : ℝ) = _
      rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
        (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
      exact congrArg (· + logNorm y) (logNorm_normSection_logEquiv (c j))
    rw [hlog, add_sub_cancel_left] at hdist
    exact hdist.le
  · refine Subtype.ext (funext fun g ↦ ?_)
    have hsum_apply : (∑ j : Fin M, bruhatLeftTranslate (h j) (ψ j)).val g =
        ∑ j : Fin M, (bruhatLeftTranslate (h j) (ψ j)).val g := by
      have hcoe (s : Finset (Fin M)) :
          (∑ j ∈ s, bruhatLeftTranslate (h j) (ψ j)).val g =
            ∑ j ∈ s, (bruhatLeftTranslate (h j) (ψ j)).val g := by
        induction s using Finset.induction_on with
        | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            exact congrArg ((bruhatLeftTranslate (h a) (ψ a)).val g + ·) ih
      exact hcoe Finset.univ
    rw [hsum_apply]
    have hterm (j : Fin M) : (bruhatLeftTranslate (h j) (ψ j)).val g = r j (logNorm g) * φ.val g := by
      simp only [ψ, bruhatLeftTranslate_apply, radialMul_apply, inv_inv, mul_inv_cancel_left]
    simp_rw [hterm, ← Finset.sum_mul]
    by_cases hg : φ.val g = 0
    · simp [hg]
    · have hsum_r : ∑ j : Fin M, r j (logNorm g) = 1 := by
        have h_eq := hdenom_eq_sum (hR_supp g hg)
        simp only [r, ← Complex.ofReal_sum, ← Finset.sum_div, ← h_eq,
          div_self (by linarith [hdenom_ge_one (logNorm g)] : denom (logNorm g) ≠ 0),
          Complex.ofReal_one]
      rw [hsum_r, one_mul]
  · intro k ω hinv j g
    simp only [ψ, bruhatLeftTranslate_apply, radialMul_apply, inv_inv]
    rw [mul_left_comm (h j) k.val⁻¹ g, logNorm_mul_ker, hinv (h j * g)]
    ring

lemma traceNorm_coshGeometric_translate_le (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (E : nuclearEndomorphisms (CoshIntervalSobolev F α s))
    (h : C𝔽) (ψ : BruhatCompactSupport C𝔽) :
    ∃ hN : IsNuclearOperator ((coshGeometricProjection (F := F) a hα hs).comp
        ((coshTestAction hα hs (bruhatLeftTranslate h ψ)).comp E.val)),
      traceNorm ⟨_, hN⟩ ≤ ‖coshLeftTranslate (F := F) hα hs h‖ *
        (traceNorm ⟨(coshSpectralProjection (F := F) a hα hs).comp
            ((coshTestAction hα hs ψ).comp E.val),
            mul_mem_nuclearEndomorphisms_left
              ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ)) E⟩ +
          traceNorm ⟨(coshGeometricProjection (F := F) a hα hs).comp
            ((coshTestAction hα hs ψ).comp E.val),
            mul_mem_nuclearEndomorphisms_left
              ((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ)) E⟩) := by
  let H := CoshIntervalSobolev F α s
  let P := coshSpectralProjection (F := F) a hα hs
  let G := coshGeometricProjection (F := F) a hα hs
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := traceNorm_normedSpaceCore (H := H)
  let Tspec : nuclearEndomorphisms H :=
    ⟨(P.comp (coshTestAction hα hs ψ)).comp E.val,
      mul_mem_nuclearEndomorphisms_left (P.comp (coshTestAction hα hs ψ)) E⟩
  let Tgeom : nuclearEndomorphisms H :=
    ⟨(G.comp (coshTestAction hα hs ψ)).comp E.val,
      mul_mem_nuclearEndomorphisms_left (G.comp (coshTestAction hα hs ψ)) E⟩
  let Lh := coshLeftTranslate (F := F) hα hs h
  have h_eq : G.comp ((coshTestAction hα hs (bruhatLeftTranslate h ψ)).comp E.val) =
      (G.comp Lh) * (Tspec + Tgeom).val := by
    rw [coshTestAction_bruhatLeftTranslate]
    change G.comp ((Lh.comp (coshTestAction hα hs ψ)).comp E.val) =
      (G.comp Lh).comp ((P.comp (coshTestAction hα hs ψ)).comp E.val +
        (G.comp (coshTestAction hα hs ψ)).comp E.val)
    rw [← ContinuousLinearMap.add_comp, ← ContinuousLinearMap.add_comp, add_comm P G,
      coshSpectralProjection_add_geometric, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
  have hN : IsNuclearOperator (G.comp ((coshTestAction hα hs (bruhatLeftTranslate h ψ)).comp E.val)) := by
    rw [h_eq]; exact mul_mem_nuclearEndomorphisms_left (G.comp Lh) (Tspec + Tgeom)
  refine ⟨hN, ?_⟩
  have htr : traceNorm ⟨G.comp ((coshTestAction hα hs (bruhatLeftTranslate h ψ)).comp E.val), hN⟩ =
      traceNorm ⟨(G.comp Lh) * (Tspec + Tgeom).val,
        mul_mem_nuclearEndomorphisms_left (G.comp Lh) (Tspec + Tgeom)⟩ :=
    congrArg traceNorm (Subtype.ext h_eq)
  rw [htr]
  refine (traceNorm_mul_left_le (G.comp Lh) (Tspec + Tgeom)).trans ?_
  have hGL : ‖G.comp Lh‖ ≤ ‖Lh‖ :=
    (ContinuousLinearMap.opNorm_comp_le G Lh).trans
      ((mul_le_mul_of_nonneg_right (norm_coshGeometricProjection_le_one a hα hs) (norm_nonneg _)).trans_eq
        (one_mul _))
  exact mul_le_mul hGL (hcore.norm_triangle Tspec Tgeom) (hcore.norm_nonneg _) (norm_nonneg _)

end RadialPartition

end RiemannMasullo.Isolated.CoshPositiveWidth
