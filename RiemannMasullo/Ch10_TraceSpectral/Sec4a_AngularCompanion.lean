module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a_Isolated
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch10_TraceSpectral.Sec3

/-! # Angular bounds for the adjoint on strip jets

The compact-test adjoint on the closed span of the jets in one norm-one character
has rapid angular decay. At Sobolev order zero the same weighted derivatives of the
test bound every center and every half-width up to a fixed maximum. Taking the
supremum of these actual operator norms gives a summable completed-Hecke divisor
majorant for the finite quotient columns of §10.4, pp. 458–461. -/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "K𝔽" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "incl" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : K𝔽 →ₜ* C𝔽)
local notation "moment(" φ "," η "," z "," q ")" =>
  (∫ g : C𝔽, (φ : BruhatCompactSupport C𝔽).val g * ideleClassNormTwist η z g *
    (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽)
local notation "jetVec(" χ "," hα "," hs "," j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp
    (spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

/-- The compact Bruhat test obtained by differentiation along a norm-one flow. -/
def spectralAngularDerivative (Y : LCATopologicalLie K𝔽) (φ : BruhatCompactSupport C𝔽) :
    BruhatCompactSupport C𝔽 :=
  ⟨bruhatDirectionalDeriv ((incl).comp Y) φ.val, ideleClass_bruhatFlowDeriv_mem _ _⟩

/-- A norm-one flow has a constant angular multiplier at every complex parameter.
Differentiating in that parameter gives the same multiplier for every logarithmic moment. -/
private theorem angularDerivative_moment (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (Y : LCATopologicalLie K𝔽)
    (φ : BruhatCompactSupport C𝔽) (ω : PontryaginDual K𝔽) (z : ℂ) (q : ℕ) :
    moment(spectralAngularDerivative Y φ, χ ω, z, q) =
      (-bruhatDirectionalDeriv Y (fun u ↦ (ω u : ℂ)) 1) * moment(φ, χ ω, z, q) := by
  let d := bruhatDirectionalDeriv Y (fun u ↦ (ω u : ℂ)) 1
  induction q generalizing z with
  | zero =>
    let c := ideleClassNormTwist (χ ω) z
    have hc (u : K𝔽) : c u.val = (ω u : ℂ) := by
      have he := DFunLike.congr_fun (hχ ω) u
      change (χ ω) u.val = ω u at he
      change ((χ ω u.val : Circle) : ℂ) * (((ideleClassNorm F u.val).val : ℝ) : ℂ) ^ z = _
      rw [u.property, he]
      simp
    let : CompactSpace K𝔽 := (ideleClassGroup_finiteness F).2.1
    have hd := hasDerivAt_bruhatDirectionalDeriv Y
      ((mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth ω) 1) 1
    simp only [one_mul] at hd
    have hflow : HasDerivAt (fun t : ℝ ↦ c (((incl).comp Y) (Multiplicative.ofAdd t))) d 0 :=
      hd.congr_of_eventuallyEq (.of_forall fun t ↦ hc (Y (Multiplicative.ofAdd t)))
    simpa only [pow_zero, mul_one, spectralAngularDerivative, neg_mul] using
      ideleClass_integral_bruhatFlowDeriv_mul ((incl).comp Y) c hflow φ
  | succ q ih =>
    have h := (hasDerivAt_ideleClass_bruhatMoment (χ ω) φ z q).const_mul (-d)
    exact (hasDerivAt_ideleClass_bruhatMoment (χ ω) (spectralAngularDerivative Y φ) z q).unique
      (h.congr_of_eventuallyEq (.of_forall ih))

section Jets

variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs φ

/-- The closed linear span of the Riesz vectors of all retained jets in one angular mode. -/
def spectralAngularJetSpace
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽)
    (r : SpectralStripJetIndex χ a α s → W)
    (ω : PontryaginDual K𝔽) : Submodule ℂ W :=
  (Submodule.span ℂ (r '' {j : (SpectralStripJetIndex χ a α s) | j.val.1 = ω})).topologicalClosure

/-- The actual adjoint, restricted in domain to the closed span of the jets in the chosen
angular mode, with values in the ambient Sobolev space. -/
def spectralAngularJetAdjoint
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽)
    (r : SpectralStripJetIndex χ a α s → W)
    (ψ : BruhatCompactSupport C𝔽) (ω : PontryaginDual K𝔽) :
    (spectralAngularJetSpace (F := F) a χ r ω) →L[ℂ] W :=
  (A(ψ)).adjoint.comp (spectralAngularJetSpace a χ r ω).subtypeL

/-- The adjoints of the angular derivative and of the original test differ on the whole
closed jet span by the conjugate of the signed angular multiplier. -/
private theorem angularDerivative_adjoint
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ)
    (r : SpectralStripJetIndex χ a α s → W)
    (hr : ∀ (j : SpectralStripJetIndex χ a α s) (f : W), inner ℂ (r j) f =
      spectralSobolevPairing (F := F) (l := -α) (r := α) (s := s) f
        (jetVec(χ,hα,hs,j)))
    (Y : LCATopologicalLie K𝔽)
    (ψ : BruhatCompactSupport C𝔽) (ω : PontryaginDual K𝔽) :
    spectralAngularJetAdjoint (F := F) a hα hs χ r (spectralAngularDerivative Y ψ) ω =
      (starRingEnd ℂ) (-bruhatDirectionalDeriv Y (fun u ↦ (ω u : ℂ)) 1) •
        spectralAngularJetAdjoint a hα hs χ r ψ ω := by
  let d := -bruhatDirectionalDeriv Y (fun u ↦ (ω u : ℂ)) 1
  have he : Set.EqOn (A(spectralAngularDerivative Y ψ)).adjoint
      ((starRingEnd ℂ) d • (A(ψ)).adjoint) (r '' {j : (SpectralStripJetIndex χ a α s) | j.val.1 = ω}) := by
    rintro _ ⟨j, hj, rfl⟩
    change j.val.1 = ω at hj
    subst ω
    change (A(spectralAngularDerivative Y ψ)).adjoint (r j) =
      (starRingEnd ℂ) d • (A(ψ)).adjoint (r j)
    rw [spectralStripJet_adjoint_testAction a hα hs χ r hr j,
      spectralStripJet_adjoint_testAction a hα hs χ r hr j, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [angularDerivative_moment χ hχ, smul_smul, ← map_mul]
    congr 2
    ring
  apply ContinuousLinearMap.ext
  intro x
  change (A(spectralAngularDerivative Y ψ)).adjoint (x : W) =
    (((starRingEnd ℂ) d) • (A(ψ)).adjoint : W →L[ℂ] W) (x : W)
  exact ContinuousLinearMap.eqOn_closure_span
    (f := (A(spectralAngularDerivative Y ψ)).adjoint)
    (g := (starRingEnd ℂ) d • (A(ψ)).adjoint) he x.property

/-- The Riesz representer of one strip jet in the original interval-Sobolev Hilbert norm. -/
def spectralAngularJetRiesz
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽)
    (j : SpectralStripJetIndex χ a α s) : W :=
  let T := (modulatedIntervalSobolev_dual m𝔽
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
    μ𝔽 (-α) α s hI hs).exists.choose
  (InnerProductSpace.toDual ℂ W).symm (T.symm ((spectralStripJet_memLp χ hα hs j).toLp
    (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)))

/-- The canonical representer recovers the Sobolev pairing against its strip jet. -/
theorem spectralAngularJetRiesz_inner
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽)
    (j : SpectralStripJetIndex χ a α s) (f : W) :
    inner ℂ (spectralAngularJetRiesz a hα hs χ j) f = spectralSobolevPairing f
      ((spectralStripJet_memLp χ hα hs j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) := by
  let T := (modulatedIntervalSobolev_dual m𝔽
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
    μ𝔽 (-α) α s hI hs).exists.choose
  let u := (spectralStripJet_memLp χ hα hs j).toLp
    (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)
  change inner ℂ ((InnerProductSpace.toDual ℂ W).symm (T.symm u)) f = spectralSobolevPairing f u
  rw [InnerProductSpace.toDual_symm_apply, (spectralSobolevPairing_dual hI hs (T.symm u) f).2]
  exact congrArg (spectralSobolevPairing f) (T.apply_symm_apply u)

/-- The canonical representers of the admitted strip jets are linearly independent. -/
theorem spectralAngularJetRiesz_linearIndependent
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) :
    LinearIndependent ℂ (spectralAngularJetRiesz a hα hs χ) := by
  let D := (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (-α) α s hI hs).exists.choose
  apply linearIndependent_iff'.mpr
  intro S c h i hi
  have h' := congrArg (fun x ↦ D (InnerProductSpace.toDual ℂ W x)) h
  simp only [map_sum, map_smulₛₗ, spectralAngularJetRiesz,
    LinearIsometryEquiv.apply_symm_apply, map_zero, D] at h'
  have hh := linearIndependent_iff'.mp (spectralStripJet_toLp_linearIndependent χ hχ a hα hs)
    S _ h' i hi
  simpa using hh

/-- At order zero all strip widths below A have the same weighted integral majorant on a fixed
compact test. Haar measure here is the original idele class Tamagawa measure. -/
private theorem testAction_norm_le_width (A : ℝ) {α : ℝ} (hα : 0 ≤ α) (hαA : α ≤ A)
    (ψ : BruhatCompactSupport C𝔽) :
    ‖(hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 ((neg_nonpos.mpr hα).trans hα)
        (le_rfl : (0 : ℝ) ≤ 0) ψ).adjoint‖ ≤
      ∫ g : C𝔽, ‖ψ.val g‖ * Real.exp (A * |logIdeleClassNorm F g|) ∂μ𝔽 := by
  let w (g : C𝔽) := Real.exp (A * |logIdeleClassNorm F g|)
  let hI₀ := (neg_nonpos.mpr hα).trans hα
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α 0 hI₀ (le_rfl : (0 : ℝ) ≤ 0)
  have hl : Continuous (logIdeleClassNorm F) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log
      (fun g ↦ NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
  have hψ : Continuous ψ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
  have hw : Continuous w := Real.continuous_exp.comp (continuous_const.mul hl.abs)
  have hi : Integrable (fun g ↦ ‖ψ.val g‖ * w g) μ𝔽 :=
    (hψ.norm.mul hw).integrable_of_hasCompactSupport
      (show HasCompactSupport ψ.val from ψ.property.2).norm.mul_right
  have hτ (g : C𝔽) : ‖τ g‖ ≤ w g := by
    apply (norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α 0 hI₀ (le_rfl : (0 : ℝ) ≤ 0) g).trans
    simp only [zero_div, Real.rpow_zero, mul_one]
    let t := logIdeleClassNorm F g
    change max (Real.exp (-α * t)) (Real.exp (α * t)) ≤ Real.exp (A * |t|)
    have htop := mul_le_mul_of_nonneg_right hαA (abs_nonneg t)
    apply max_le
    · apply Real.exp_le_exp.mpr
      rw [neg_mul, ← mul_neg]
      exact (mul_le_mul_of_nonneg_left (neg_le_abs t) hα).trans htop
    · exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (le_abs_self t) hα).trans htop)
  let V := CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α 0
  let op : V →L[ℂ] V := hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 hI₀ le_rfl ψ
  change ‖op.adjoint‖ ≤ _
  rw [ContinuousLinearMap.adjoint.norm_map op]
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun g ↦
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  intro u
  rw [hardySobolev_eq_integral_translation_of_convolution μ𝔽 m𝔽 (-α) α 0 hI₀
    (le_rfl : (0 : ℝ) ≤ 0) (hψ.integrable_of_hasCompactSupport ψ.property.2) ψ.property.2
    op (hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α 0 hI₀ le_rfl ψ) u]
  change ‖∫ g, ψ.val g • τ g u ∂μ𝔽‖ ≤ (∫ g, ‖ψ.val g‖ * w g ∂μ𝔽) * ‖u‖
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le (hi.mul_const ‖u‖)
  exact .of_forall fun g ↦ by
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (((τ g).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hτ g) (norm_nonneg _))) (norm_nonneg _)

/-- A width-uniform upper bound built from finitely many weighted L¹ norms of iterated
compact angular derivatives. At level n+1 every derivative used has order at most n+1. -/
def spectralAngularWidthBound {ι : Type*} [Fintype ι] (Y : ι → LCATopologicalLie K𝔽) (A : ℝ) :
    ℕ → BruhatCompactSupport C𝔽 → ℝ
  | 0, φ => ∫ g : C𝔽, ‖φ.val g‖ * Real.exp (A * |logIdeleClassNorm F g|) ∂μ𝔽
  | n + 1, φ => spectralAngularWidthBound Y A n φ +
      ∑ i, spectralAngularWidthBound Y A n (spectralAngularDerivative (Y i) φ)

private theorem widthBound_nonneg {ι : Type*} [Fintype ι] (Y : ι → LCATopologicalLie K𝔽)
    (A : ℝ) (n : ℕ) (ψ : BruhatCompactSupport C𝔽) : 0 ≤ spectralAngularWidthBound Y A n ψ := by
  induction n generalizing ψ with
  | zero => exact integral_nonneg fun g ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  | succ n ih => exact add_nonneg (ih ψ) (Finset.sum_nonneg fun i _ ↦ ih _)

/-- At order zero the same explicit test bound works for all centers, all widths from zero
up to A, every choice of angular lifts, every mode and every retained Jordan order. -/
theorem spectralAngularJetAdjoint_le_widthBound (a α A : ℝ) (hα : 0 ≤ α) (hαA : α ≤ A)
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (r : SpectralStripJetIndex χ a α 0 →
      CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α 0)
    (hr : ∀ (j : SpectralStripJetIndex χ a α 0)
      (f : CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α 0), inner ℂ (r j) f =
        spectralSobolevPairing (F := F) (l := -α) (r := α) (s := 0) f
          (jetVec(χ,hα,le_rfl,j)))
    {ι : Type*} [Fintype ι] (Y : ι → LCATopologicalLie K𝔽)
    (ψ : BruhatCompactSupport C𝔽) (N : ℕ) (ω : PontryaginDual K𝔽) :
    ‖spectralAngularJetAdjoint a hα le_rfl χ r ψ ω‖ *
      (1 + ((Finset.univ.sup (fun i ↦ ‖bruhatDirectionalDeriv (Y i) (fun u ↦ (ω u : ℂ)) 1‖₊)
        : ℝ≥0) : ℝ)) ^ N ≤ spectralAngularWidthBound Y A N ψ := by
  classical
  let K (φ : BruhatCompactSupport C𝔽) := ‖spectralAngularJetAdjoint a hα le_rfl χ r φ ω‖
  let d (i : ι) := bruhatDirectionalDeriv (Y i) (fun u ↦ (ω u : ℂ)) 1
  let H : ℝ := ↑(Finset.univ.sup (fun i ↦ ‖d i‖₊))
  have hbase (φ : BruhatCompactSupport C𝔽) : K φ ≤ spectralAngularWidthBound Y A 0 φ := by
    let T := (hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 ((neg_nonpos.mpr hα).trans hα) le_rfl φ).adjoint
    calc
      K φ ≤ ‖T‖ * ‖(spectralAngularJetSpace a χ r ω).subtypeL‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖ :=
        ((mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le _) (norm_nonneg _)).trans_eq
          (mul_one _))
      _ ≤ spectralAngularWidthBound Y A 0 φ := testAction_norm_le_width A hα hαA φ
  have hmul (i : ι) (φ : BruhatCompactSupport C𝔽) : K (spectralAngularDerivative (Y i) φ) =
      ‖d i‖ * K φ := by
    dsimp only [K]
    rw [angularDerivative_adjoint a hα le_rfl χ hχ r hr, norm_smul]
    simp only [Complex.norm_conj, norm_neg, d]
  change K ψ * (1 + H) ^ N ≤ spectralAngularWidthBound Y A N ψ
  induction N generalizing ψ with
  | zero => simpa only [pow_zero, mul_one] using hbase ψ
  | succ n ih =>
    have hgain : (H * K ψ) * (1 + H) ^ n ≤
        ∑ i, spectralAngularWidthBound Y A n (spectralAngularDerivative (Y i) ψ) := by
      by_cases hi : Nonempty ι
      · have := hi
        obtain ⟨i, _, he⟩ := Finset.univ.exists_mem_eq_sup Finset.univ_nonempty (fun i ↦ ‖d i‖₊)
        have he' : H = ‖d i‖ := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) he
        rw [(congrArg (· * K ψ) he').trans (hmul i ψ).symm]
        exact (ih _).trans (Finset.single_le_sum
          (fun j _ ↦ widthBound_nonneg Y A n (spectralAngularDerivative (Y j) ψ))
            (Finset.mem_univ i))
      · have : IsEmpty ι := not_nonempty_iff.mp hi
        simp [H]
    calc
      K ψ * (1 + H) ^ (n + 1) = K ψ * (1 + H) ^ n + (H * K ψ) * (1 + H) ^ n := by ring
      _ ≤ _ := add_le_add (ih ψ) hgain

end Jets

/-- The norm-one restriction of a Hecke character, in the angular coordinates of the jets. -/
def spectralAngularChartMode (η : PontryaginDual C𝔽) : PontryaginDual K𝔽 :=
  η.comp incl

/-- Lift a norm-one character along the projection `g ↦ g / τ (|g|)` attached to the section. -/
def spectralAngularNormalizedLift (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (ω : PontryaginDual K𝔽) : PontryaginDual C𝔽 :=
  let p : C𝔽 →ₜ* C𝔽 := ContinuousMonoidHom.id C𝔽 / τ.comp m𝔽
  let hp (x : C𝔽) : p x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, hτ, div_self']
  ω.comp ⟨p.toMonoidHom.codRestrict _ hp, p.continuous.subtype_mk _⟩

/-- Restriction to the norm-one subgroup recovers the input angular character. -/
theorem spectralAngularNormalizedLift_basepoint (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    IsSpectralBasepointChoice (spectralAngularNormalizedLift τ hτ) := by
  intro ω
  ext u : 1
  apply congrArg ω
  apply Subtype.ext
  change u.val / τ (ideleClassNorm F u.val) = u.val
  rw [u.property, map_one, div_one]

/-- For a character normalized on the same section, lifting its norm-one restriction
recovers that character itself, with no imaginary shift of the spectral coordinate. -/
theorem spectralAngularNormalizedLift_chartMode (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F))
    (η : {η : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1}) :
    spectralAngularNormalizedLift τ hτ (spectralAngularChartMode η.val) = η.val := by
  ext g : 1
  change η.val (g / τ (ideleClassNorm F g)) = η.val g
  rw [map_div, η.property, div_one]

/-- The real mode envelope used in the chart-character summability criterion at order zero.
It is the operator norm of the actual adjoint on the canonical Riesz span. -/
def spectralAngularChartNorm (a α : ℝ) (hα : 0 ≤ α)
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (ψ : BruhatCompactSupport C𝔽)
    (η : PontryaginDual C𝔽) : ℝ :=
  ‖spectralAngularJetAdjoint a hα le_rfl χ (spectralAngularJetRiesz a hα le_rfl χ) ψ
    (spectralAngularChartMode η)‖

/-- A norm-one period with a nontrivial character kills every logarithmic Mellin moment. -/
private theorem moment_eq_zero_of_period (φ : BruhatCompactSupport C𝔽) (k : Subgroup C𝔽)
    (hk : k ≤ (ideleClassNorm F).ker) (hper : ∀ u : k, ∀ g, φ.val (u.val * g) = φ.val g)
    (η : PontryaginDual C𝔽) (hoff : ¬ ∀ u : k, η u.val = 1) (z : ℂ) (q : ℕ) :
    moment(φ, η, z, q) = 0 := by
  obtain ⟨u, hu⟩ := not_forall.mp hoff
  have hN : ideleClassNorm F u.val = 1 := hk u.property
  let c := ideleClassNormTwist η z
  let p (g : C𝔽) := (logIdeleClassNorm F g : ℂ) ^ q
  let f (g : C𝔽) := φ.val g * c g * p g
  have hc : c u.val = (η u.val : ℂ) := by
    change (η u.val : ℂ) * (((ideleClassNorm F u.val).val : ℝ) : ℂ) ^ z = _
    simp [hN]
  have hp (g : C𝔽) : p (u.val * g) = p g := by
    simp only [p, logIdeleClassNorm, map_mul, hN, one_mul]
  have hshift (g : C𝔽) : f (u.val * g) = (η u.val : ℂ) * f g := by
    dsimp only [f]
    rw [hper, map_mul, hc, hp]
    ring
  change (∫ g, f g ∂μ𝔽) = 0
  by_contra hm
  have he := integral_mul_left_eq_self (μ := μ𝔽) f u.val
  simp_rw [hshift, integral_const_mul] at he
  exact hu (Circle.ext ((mul_eq_right₀ hm).mp he))

/-- A nontrivial period kills the adjoint on the whole closed angular jet span. -/
private theorem chartNorm_eq_zero_of_period (a α : ℝ) (hα : 0 ≤ α)
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (φ : BruhatCompactSupport C𝔽) (k : Subgroup C𝔽) (hk : k ≤ (ideleClassNorm F).ker)
    (hper : ∀ u : k, ∀ g, φ.val (u.val * g) = φ.val g)
    (η : PontryaginDual C𝔽) (hoff : ¬ ∀ u : k, η u.val = 1) :
    spectralAngularChartNorm a α hα χ φ η = 0 := by
  let ω := spectralAngularChartMode η
  have hoff' : ¬ ∀ u : k, χ ω u.val = 1 := by
    intro h
    apply hoff
    intro u
    have he := DFunLike.congr_fun (hχ ω) (⟨u.val, hk u.property⟩ : K𝔽)
    change χ ω u.val = η u.val at he
    exact he.symm.trans (h u)
  let r := spectralAngularJetRiesz a hα le_rfl χ
  let W := CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α 0
  let T := (hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα) le_rfl φ).adjoint
  have he : Set.EqOn T (0 : W →L[ℂ] W) (r '' {j : SpectralStripJetIndex χ a α 0 | j.val.1 = ω}) := by
    rintro _ ⟨j, hj, rfl⟩
    change j.val.1 = ω at hj
    change T (r j) = 0
    rw [show T (r j) = _ from spectralStripJet_adjoint_testAction a hα le_rfl χ r
      (spectralAngularJetRiesz_inner a hα le_rfl χ) j φ]
    apply Finset.sum_eq_zero
    intro i _
    have hz (z : ℂ) (q : ℕ) : moment(φ, χ j.val.1, z, q) = 0 :=
      hj ▸ moment_eq_zero_of_period φ k hk hper (χ ω) hoff' z q
    rw [hz]
    simp
  apply norm_eq_zero.mpr
  apply ContinuousLinearMap.ext
  exact fun x ↦ ContinuousLinearMap.eqOn_closure_span he x.property

local notation "widthValues(" A "," ψ "," η ")" =>
  {v : ℝ | v = 0 ∨ ∃ (a α : ℝ) (hα : 0 ≤ α), α ≤ A ∧
    ∃ χ : PontryaginDual K𝔽 → PontryaginDual C𝔽,
      IsSpectralBasepointChoice χ ∧ v = spectralAngularChartNorm a α hα χ ψ η}

/-- The supremum of the actual modal adjoint norms over all centers, admissible lifts and
half-widths from zero to `A`. The included zero also covers an empty interval of widths. -/
def spectralAngularWidthEnvelope (A : ℝ) (ψ : BruhatCompactSupport C𝔽) (η : PontryaginDual C𝔽) : ℝ :=
  sSup widthValues(A,ψ,η)

private theorem widthNormValues_bddAbove (A : ℝ) (ψ : BruhatCompactSupport C𝔽)
    (η : PontryaginDual C𝔽) : BddAbove widthValues(A,ψ,η) := by
  let Ys (_ : Unit) : LCATopologicalLie K𝔽 := 1
  refine ⟨spectralAngularWidthBound Ys A 0 ψ, fun v hv ↦ ?_⟩
  rcases hv with rfl | ⟨a, α, hα, hαA, χ, hχ, rfl⟩
  · exact widthBound_nonneg Ys A 0 ψ
  · have h := spectralAngularJetAdjoint_le_widthBound a α A hα hαA χ hχ _
      (spectralAngularJetRiesz_inner a hα le_rfl χ) Ys ψ 0 (spectralAngularChartMode η)
    simpa only [spectralAngularChartNorm, pow_zero, mul_one] using h

/-- Every width envelope includes zero among its defining values. -/
private theorem widthEnvelope_nonneg (A : ℝ) (ψ : BruhatCompactSupport C𝔽)
    (η : PontryaginDual C𝔽) : 0 ≤ spectralAngularWidthEnvelope A ψ η :=
  le_csSup (widthNormValues_bddAbove A ψ η) (Or.inl rfl)

/-- The common envelope dominates the actual norm for every admissible center and width. -/
theorem spectralAngularChartNorm_le_widthEnvelope (A a α : ℝ) (hα : 0 ≤ α) (hαA : α ≤ A)
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (ψ : BruhatCompactSupport C𝔽) (η : PontryaginDual C𝔽) :
    spectralAngularChartNorm a α hα χ ψ η ≤ spectralAngularWidthEnvelope A ψ η :=
  le_csSup (widthNormValues_bddAbove A ψ η) (Or.inr ⟨a, α, hα, hαA, χ, hχ, rfl⟩)

/-- The supremum over all strips satisfies the same explicit finite-direction estimate as each strip. -/
private theorem widthEnvelope_mul_le_widthBound (A : ℝ) {ι : Type*} [Fintype ι]
    (Y : ι → LCATopologicalLie K𝔽) (φ : BruhatCompactSupport C𝔽) (N : ℕ)
    (η : PontryaginDual C𝔽) :
    spectralAngularWidthEnvelope A φ η *
        (1 + ((Finset.univ.sup (fun i ↦
          ‖bruhatDirectionalDeriv (Y i) (fun u ↦ (spectralAngularChartMode η u : ℂ)) 1‖₊)
          : ℝ≥0) : ℝ)) ^ N ≤ spectralAngularWidthBound Y A N φ := by
  let H : ℝ := ↑(Finset.univ.sup (fun i ↦
    ‖bruhatDirectionalDeriv (Y i) (fun u ↦ (spectralAngularChartMode η u : ℂ)) 1‖₊))
  have hH : 0 < (1 + H)^N := pow_pos (add_pos_of_pos_of_nonneg one_pos (NNReal.coe_nonneg _)) N
  apply (le_div_iff₀ hH).mp
  apply csSup_le ⟨0, Or.inl rfl⟩
  intro v hv
  rcases hv with rfl | ⟨a, α, hα, hαA, χ, hχ, rfl⟩
  · exact div_nonneg (widthBound_nonneg Y A N φ) hH.le
  · exact (le_div_iff₀ hH).mpr (spectralAngularJetAdjoint_le_widthBound a α A hα hαA χ hχ _
      (spectralAngularJetRiesz_inner a hα le_rfl χ) Y φ N (spectralAngularChartMode η))

/-- Full completed-Hecke divisor order divided by the inverse-square height denominator. -/
def spectralAngularDivisorHeightWeight (η : PontryaginDual C𝔽) (z : ℂ) : ℝ :=
  (MeromorphicOn.divisor (explicitFormulaCompletedHeckeL η) Set.univ z : ℝ) / (1 + z.im ^ 2)

local notation "chartRows(" τ ")" =>
  {η : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local notation "allZeros(" η ")" =>
  {z : ℂ // 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (η).val) Set.univ z}
local notation "divisorPairs(" τ ")" => (Σ η : chartRows(τ), allZeros(η))

/-- A single summable divisor-height envelope, over every chart character and every true zero
with its full order, simultaneously bounds the squared angular factors for all strip widths. -/
theorem spectralAngularWidthEnvelope_summable_fullDivisor (A : ℝ) (ψ : BruhatCompactSupport C𝔽)
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    Summable (fun p : divisorPairs(τ) ↦ spectralAngularWidthEnvelope A ψ p.1.val ^ 2 *
      spectralAngularDivisorHeightWeight p.1.val p.2.val) := by
  obtain ⟨k, hk, hper, _⟩ := (mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1 0
  have hk₁ : k ≤ (ideleClassNorm F).ker := compactSubgroup_le_modulation_ker m𝔽 k hk.isCompact
  apply explicitFormulaCompletedHeckeL_summable_angular_divisor_div_one_add_im_sq τ hτ k hk
    (fun η ↦ spectralAngularWidthEnvelope A ψ η.val)
  · intro η hinact
    refine le_antisymm (csSup_le ⟨0, Or.inl rfl⟩ ?_) (widthEnvelope_nonneg A ψ η.val)
    intro v hv
    rcases hv with rfl | ⟨a, α, hα, _, χ, hχ, rfl⟩
    · exact le_rfl
    · exact (chartNorm_eq_zero_of_period a α hα χ hχ ψ k hk₁ hper η.val hinact).le
  · intro Y N
    let Ys (_ : Unit) := Y
    refine ⟨spectralAngularWidthBound Ys A N ψ, widthBound_nonneg Ys A N ψ, fun η _ ↦ ?_⟩
    let d := ‖bruhatDirectionalDeriv Y (fun u : K𝔽 ↦ (η.val u.val : ℂ)) 1‖
    have hb := widthEnvelope_mul_le_widthBound A Ys ψ N η.val
    have hd : d ≤ 1 + d := le_add_of_nonneg_left zero_le_one
    rw [abs_of_nonneg (widthEnvelope_nonneg A ψ η.val), mul_comm]
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd N)
      (widthEnvelope_nonneg A ψ η.val)).trans
    change spectralAngularWidthEnvelope A ψ η.val * (1 + ((Finset.univ.sup (fun _ : Unit ↦
      ‖bruhatDirectionalDeriv Y (fun u : K𝔽 ↦ (η.val u.val : ℂ)) 1‖₊) : ℝ≥0) : ℝ)) ^ N ≤ _ at hb
    simpa only [Finset.univ_unique, Finset.sup_singleton, coe_nnNorm, d] using hb

end RiemannMasullo.Isolated
