module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppA_AlgebraicNT.Sec1
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
import all RiemannMasullo.AppC_LCTVS.Sec3a_part2
import RiemannMasullo.Ch09_HardySobolev.Sec3

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b

/-! # Sobolev Paley–Wiener levels and orbital nuclearity

Masullo, §§11.2.1–11.2.2, pp. 487–491. The stage parameter lists the finite
places, with every archimedean place included implicitly.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "mₛ(" S ")" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "h₀" => (le_rfl (a := (0 : ℝ)))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 (logNorm(m𝔽)) 0 0 s
local notation "Wω(" hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 _ h₀ hs).comp
    (ideleClassNorm F).ker.subtype) ω
local notation "ω(" χ ")" =>
  (χ : PontryaginDual C𝔽).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    C₁ →ₜ* C𝔽)
local notation "A(" hs ", " φ ")" => hardySobolevTestAction μ𝔽 m𝔽 0 0 _ h₀ hs φ
local notation "supportedAboveOne(" φ ")" =>
  (tsupport (φ : BruhatCompactSupport C𝔽).val ⊆ {g | 1 ≤ ((m𝔽 g).val : ℝ)})

section Levels

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ} (hs : 0 ≤ s)

-- Use the base [-0, 0] of §10.4 for its geometric projection and cutoff.
local notation "hGeo" => (neg_nonpos.mpr h₀ |>.trans h₀)
local notation "GeoIsotype(" ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs).comp
    (ideleClassNorm F).ker.subtype) ω
local notation "geoAction(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs φ

local notation "Zₛ" => sAdelePolarSubspace F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "band(" K ")" =>
  ({f : Zₛ | f.val ∈ sLocalPWTests (S := S) (T := S) le_rfl K} : Set Zₛ)
local notation "localWeightedTheta(" a ", " ω ", " f ")" =>
  modulationWeight (mₛ(S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω (f : Zₛ).val)
local notation "globalWeightedTheta(" a ", " ω ", " f ")" =>
  modulationWeight m𝔽 a (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F S (f : Zₛ).val))

local notation "localWMeasure" => (sLocalQuotientTamagawaMeasure F S).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm(mₛ(S)) g)))
local notation "globalWMeasure" => (μ𝔽).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm(m𝔽) g)))
local notation "GeoW" => Lp ℂ 2 globalWMeasure
local notation "LocalW" => Lp ℂ 2 localWMeasure

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Local polar-free tests yield Sobolev vectors at positive twist.
Deviation: Use the positive range of the local Sobolev embedding from §10.1. -/
theorem sLocalPWTheta_memLp {a : ℝ} (_ha : 0 < a) (ω : PontryaginDual J₁) (f : Zₛ) :
    MemLp (localWeightedTheta(a, ω, f)) 2 localWMeasure := by
  let : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
  let μ := sLocalQuotientTamagawaMeasure F S
  let r (g : SIdeleQuotient F S) : ℝ := (mₛ(S) g).val
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f.val
  let t := max s 0
  let b := a / 2
  have hb : 0 < b := half_pos _ha
  have hbb : b + b = a := add_halves a
  have hr (g) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hc : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ(S)).continuous)
  obtain ⟨j, -, -, hj⟩ := exists_sLocalHomogeneousThetaSobolevInclusion (F := F) (S := S)
    hb (le_refl b) (show 0 ≤ t from le_max_right _ _) hb ω
  let u := (j (Submodule.Quotient.mk f.val)).val.val
  have hi := (globalThetaSobolev_norm_aux μ r hr hc.measurable b b b t θ u (hj f.val).2).1
  rw [hbb] at hi
  let d (g : SIdeleQuotient F S) := intervalSobolevDensity 0 0 t (Real.log (r g))
  have hd (g) : 0 ≤ d g := by dsimp [d, intervalSobolevDensity]; positivity
  have hm : Measurable d := by dsimp [d, intervalSobolevDensity]; fun_prop
  let Z (g : SIdeleQuotient F S) : ℂ := ((r g ^ a : ℝ) : ℂ) * θ g
  have hZ : Continuous Z := (Complex.continuous_ofReal.comp (hc.rpow_const fun g ↦ Or.inl (hr g).ne')).mul θ.continuous
  have mem : MemLp Z 2 (μ.withDensity fun g ↦ ENNReal.ofReal (d g)) := by
    apply (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).2
    apply (integrable_withDensity_iff_integrable_smul' (ENNReal.measurable_ofReal.comp hm)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine hi.congr (.of_forall fun g ↦ ?_)
    change ‖θ g‖ ^ 2 * intervalSobolevDensity a a t (Real.log (r g)) =
      (ENNReal.ofReal (d g)).toReal • ‖Z g‖ ^ 2
    rw [ENNReal.toReal_ofReal (hd g), smul_eq_mul]
    simp only [Z, d, norm_mul, mul_pow, Complex.norm_real,
      Real.rpow_def_of_pos (hr g), Real.norm_of_nonneg (Real.exp_pos _).le]
    have he := globalThetaSobolev_norm_density a 0 0 t (Real.log (r g))
    simp only [add_zero] at he
    rw [← he, mul_comm (Real.log (r g)) a]
    ring
  apply mem.mono_measure (withDensity_mono (.of_forall fun g ↦ ?_))
  apply ENNReal.ofReal_le_ofReal
  unfold d intervalSobolevDensity
  apply mul_le_mul_of_nonneg_left _ (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.log (r g))])
    (div_le_div_of_nonneg_right (le_max_left s 0) (by norm_num))

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Send a local polar-free test to its weighted homogeneous theta class.
Deviation: Use the positive local twist of the Sobolev embedding. -/
def sLocalPWThetaSobolevMap {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁)
    (f : Zₛ) :=
  MemLp.toLp (localWeightedTheta(a, ω, f))
    (sLocalPWTheta_memLp (F := F) (S := S) (s := s) ha ω f)

private theorem sLocalPWThetaSobolevMap_apply_ae_of_withDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ} (hm : AEMeasurable w μ) (hw : ∀ x, 0 < w x) {P : α → Prop}
    (h : ∀ᵐ x ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)), P x) : ∀ᵐ x ∂μ, P x := by
  have := (withDensity_absolutelyContinuous' (μ := μ) (f := fun x ↦ ENNReal.ofReal (w x))
    hm.ennreal_ofReal (Filter.Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.2 (hw x)).ne'))
  exact this.ae_le h

private theorem sLocalPWThetaSobolevMap_apply_dens_pos (a b s t : ℝ) :
    0 < intervalSobolevDensity a b s t :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

private theorem sLocalPWThetaSobolevMap_apply_dens_meas (a b s : ℝ) :
    Measurable (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  fun_prop

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
The local Sobolev map is represented almost everywhere by the weighted homogeneous theta. -/
theorem sLocalPWThetaSobolevMap_apply {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (f : Zₛ) :
    (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f : SIdeleQuotient F S → ℂ) =ᵐ[sLocalQuotientTamagawaMeasure F S]
      localWeightedTheta(a, ω, f) := by
  have : OpensMeasurableSpace (SIdeleQuotient F S) := ⟨le_of_eq rfl⟩
  have hm : Measurable (fun g : SIdeleQuotient F S ↦ Real.log (((mₛ(S)) g).val : ℝ)) :=
    Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
      ((Units.continuous_val.comp (mₛ(S)).continuous).measurable))
  exact sLocalPWThetaSobolevMap_apply_ae_of_withDensity
    ((sLocalPWThetaSobolevMap_apply_dens_meas 0 0 s).comp hm).aemeasurable
    (fun _ ↦ sLocalPWThetaSobolevMap_apply_dens_pos _ _ _ _) (MemLp.coeFn_toLp _)

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
Globalized polar-free tests yield weighted Sobolev vectors.
Deviation: Use direct integer-indicator insertion as in the repaired §7.3.2. -/
theorem globalPWTheta_memLp (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    MemLp (globalWeightedTheta(a, ω, f)) 2 globalWMeasure := by
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo (le_max_right s 0) ω
  have he := (hj f₀ x rfl).2
  have hv := (Lp.memLp (j x).val.val).ae_eq ((withDensity_absolutelyContinuous _ _).ae_le he)
  apply hv.mono_measure (withDensity_mono (Filter.Eventually.of_forall fun g ↦ ?_))
  apply ENNReal.ofReal_le_ofReal
  unfold intervalSobolevDensity
  apply mul_le_mul_of_nonneg_left _ (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (logNorm(m𝔽) g)])
    (div_le_div_of_nonneg_right (le_max_left s 0) (by norm_num))

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
Insert a local polar-free test and take its weighted global homogeneous theta class.
Deviation: Use direct integer-indicator insertion as in the repaired §7.3.2. -/
def globalPWThetaSobolevMap (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :=
  MemLp.toLp (globalWeightedTheta(a, ω, f))
    (globalPWTheta_memLp (F := F) (S := S) (s := s) a ω f)

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
The global Sobolev map is represented almost everywhere by the weighted homogeneous theta. -/
theorem globalPWThetaSobolevMap_apply (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    (globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f : C𝔽 → ℂ) =ᵐ[μ𝔽]
      globalWeightedTheta(a, ω, f) := by
  have hm : Measurable (fun g : C𝔽 ↦ Real.log (((m𝔽) g).val : ℝ)) :=
    Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
      ((Units.continuous_val.comp (m𝔽).continuous).measurable))
  exact sLocalPWThetaSobolevMap_apply_ae_of_withDensity
    ((sLocalPWThetaSobolevMap_apply_dens_meas (-(0 : ℝ)) 0 s).comp hm).aemeasurable
    (fun _ ↦ sLocalPWThetaSobolevMap_apply_dens_pos _ _ _ _) (MemLp.coeFn_toLp _)

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), p. 487.
The local absolute level is the weighted Sobolev closure of homogeneous theta
from zero-moment tests whose Fourier transforms lie in the box of size Λ.
Deviation: Use a positive local twist so the weighted theta functions belong to L². -/
def sLocalAbsolutePWSobolev (_hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) :
    Submodule ℂ LocalW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWBox S Λ) ↦
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), p. 487.
A box-limited polar-free test gives its weighted homogeneous theta vector in the local level.
Deviation: Use the positive local twist of the repaired definition. -/
theorem sLocalAbsolutePWSobolev_mem {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWBox S Λ)) :
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalAbsolutePWSobolev (F := F) (S := S) hs ha ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

-- TODO(paper-gap): (11.2.1.2) leaves X free. The box parameter here is Λ,
-- as indicated by the comparison with Λ^|S| in the proof on p. 489.

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.2), p. 487.
The global absolute level is the Sobolev closure of the weighted homogeneous
theta image of the box-limited polar-free tests.
Deviation: Use X = Λ as in the comparison on p. 489. Insert directly from S
with the integer indicators of §7.3.2. Factoring this insertion at S′
gives the same global tests and preserves the two zero moments. -/
def globalAbsolutePWSobolev (_hs : 0 ≤ s) (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    Submodule ℂ GeoW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWBox S Λ) ↦
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.2), p. 487.
An inserted box-limited polar-free test gives its weighted homogeneous theta
vector in the global level.
Deviation: Use X = Λ and the direct integer-indicator insertion. -/
theorem globalAbsolutePWSobolev_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWBox S Λ)) :
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

local notation "ambientGeom(" a ")" => geometricProjection (F := F) a h₀ hs
local notation "onIsotype(" ω ", " T ")" =>
  (GeoIsotype(ω)).orthogonalProjectionOnto.comp ((T).comp (GeoIsotype(ω)).subtypeL)
local notation "absLevel(" a ", " ω ", " Λ ")" =>
  (globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ).comap (GeoIsotype(ω)).subtype

-- TODO(paper-gap): (11.2.1.3) gives the PW level as the codomain but
-- describes the projection using the undefined HS_{Λ₀}. The definition
-- below follows the declared codomain and the proof of Theorem 11.2.1.2.

/-- Paper: Definition 11.2.1.1(2) and (11.2.1.3), p. 488.
The absolute truncation is the orthogonal projection onto the global absolute level.
Deviation: Use the level of (11.2.1.2) for the undefined HS symbol and include
the projected vector back into the ambient isotype. -/
def absolutePWProjection (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  letI : IsClosed (absLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  (absLevel(a, ω, Λ)).starProjection

/-- Paper: Definition 11.2.1.1(2), p. 488.
The absolute projection fixes vectors in the absolute level. -/
theorem absolutePWProjection_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (u : GeoIsotype(ω)) (_hu : u ∈ absLevel(a, ω, Λ)) :
    absolutePWProjection (F := F) (S := S) hs a ω Λ u = u := by
  letI : IsClosed (absLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Definition 11.2.1.1(3), p. 488.
Absolute condensation first projects onto the absolute level, then convolves
and projects onto the weighted theta subspace. -/
def absolutePWCondensation (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ)) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  (onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ)))).comp
    (absolutePWProjection (F := F) (S := S) hs a ω Λ)

/-- Paper: Definition 11.2.1.1(3), p. 488.
On the absolute level, condensation acts by convolution followed by the geometric projection. -/
theorem absolutePWCondensation_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (hφ : supportedAboveOne(φ))
    (u : GeoIsotype(ω)) (_hu : u ∈ absLevel(a, ω, Λ)) :
    absolutePWCondensation (F := F) (S := S) hs a ω Λ φ hφ u =
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by
  have h := absolutePWProjection_apply_of_mem (F := F) (S := S) hs a ω Λ u _hu
  simp only [absolutePWCondensation, ContinuousLinearMap.comp_apply, h]

local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "Pgeom(" a ", " ω ")" => onIsotype(ω, ambientGeom(a))

/-- Monotone closed levels inside `I`, whose closed union is `K ∩ I`, have compressed projection
limit when the projection onto `K` preserves `I`. -/
private theorem absolutePWProjection_tendsto_limit
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)] (hmono : Monotone levels)
    (hK : ∀ u : I, K.starProjection (u : H) ∈ I)
    (hle : ∀ i, levels i ≤ K.comap I.subtype)
    (hdense : K.comap I.subtype ≤ (⨆ i, levels i).topologicalClosure) (u : I) :
    Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
  have hKc : IsClosed (K : Set H) := (completeSpace_coe_iff_isComplete.mp ‹CompleteSpace K›).isClosed
  have hclosed : IsClosed (K.comap I.subtype : Set I) := hKc.preimage continuous_subtype_val
  have hsub : (⨆ i, levels i).topologicalClosure ≤ K.comap I.subtype :=
    Submodule.topologicalClosure_minimal _ (iSup_le hle) hclosed
  haveI : CompleteSpace ((⨆ i, levels i).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have h := Submodule.starProjection_tendsto_closure_iSup levels hmono u
  let v : I := ⟨K.starProjection (u : H), hK u⟩
  have hvm : v ∈ (⨆ i, levels i).topologicalClosure :=
    hdense (Submodule.mem_comap.mpr (K.starProjection_apply_mem (u : H)))
  have hvo : ∀ w ∈ (⨆ i, levels i).topologicalClosure, inner ℂ ((u : I) - v) w = 0 := by
    intro w hw
    rw [Submodule.coe_inner, Submodule.coe_sub]
    exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_comap.mp (hsub hw))
      (K.sub_starProjection_mem_orthogonal (u : H))
  have hp : (⨆ i, levels i).topologicalClosure.starProjection u =
      I.orthogonalProjectionOnto (K.starProjection u) := by
    rw [show K.starProjection (u : H) = (v : H) from rfl,
      I.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hvm hvo
  rw [hp] at h
  exact h

/-- The global absolute levels increase with the box size. -/
private theorem absolutePWProjection_tendsto_mono (a : ℝ) (ω : PontryaginDual C₁) {Λ Λ' : ℝ}
    (h : Λ ≤ Λ') :
    globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ ≤
      globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ' := by
  have hbox : sLocalPWBox S Λ ⊆ sLocalPWBox S Λ' := fun _ hx ↦
    ⟨fun w ↦ (hx.1 w).trans h, fun v ↦ (hx.2 v).trans h⟩
  have htests : sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ) ≤
      sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ') :=
    Submodule.map_mono (Submodule.span_mono fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩)
  apply Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f.val, htests f.2⟩, rfl⟩

/-- An orthogonal projection commutes with an invertible contraction whose inverse is a
contraction, when both preserve the subspace. -/
private theorem absolutePWProjection_tendsto_commute
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (U W : H →L[ℂ] H)
    (hWU : ∀ x, W (U x) = x) (hUW : ∀ x, U (W x) = x)
    (hU : ∀ x, ‖U x‖ ≤ ‖x‖) (hW : ∀ x, ‖W x‖ ≤ ‖x‖)
    (hUK : ∀ x ∈ K, U x ∈ K) (hWK : ∀ x ∈ K, W x ∈ K) (x : H) :
    K.starProjection (U x) = U (K.starProjection x) := by
  have hiso (y : H) : ‖U y‖ = ‖y‖ := by
    refine le_antisymm (hU y) ?_
    have h := hW (U y)
    rwa [hWU] at h
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := U.toLinearMap, norm_map' := hiso }
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hUK _ (K.starProjection_apply_mem x))
  intro w hw
  have h2 : L (x - K.starProjection x) = U x - U (K.starProjection x) := map_sub U _ _
  have h3 : L (W w) = w := hUW w
  rw [← h2, ← h3, L.inner_map_map]
  exact Submodule.inner_left_of_mem_orthogonal (hWK w hw) (K.sub_starProjection_mem_orthogonal x)

/-- A closed subspace preserved by a unitary group action is preserved by its orthogonal
projection, so the projection preserves every isotype of the action. -/
private theorem absolutePWProjection_tendsto_isotype
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Type*) [CommGroup G] [TopologicalSpace G] (ρ : G →* (H →L[ℂ] H))
    (K : Submodule ℂ H) [CompleteSpace K]
    (hK : ∀ g x, x ∈ K → ρ g x ∈ K)
    (hU : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (ω : PontryaginDual G) (u : actionIsotype ρ ω) :
    K.starProjection (u : H) ∈ actionIsotype ρ ω := by
  have hinv (g : G) (x : H) : ρ g⁻¹ (ρ g x) = x := by
    show (ρ g⁻¹ * ρ g) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hinv' (g : G) (x : H) : ρ g (ρ g⁻¹ x) = x := by
    show (ρ g * ρ g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [mem_actionIsotype]
  intro g
  have hu : ρ g (u : H) = (ω g : ℂ) • (u : H) := (mem_actionIsotype ρ ω (u : H)).mp u.property g
  have hc := absolutePWProjection_tendsto_commute H K (ρ g) (ρ g⁻¹) (hinv g) (hinv' g)
    (hU g) (hU g⁻¹) (hK g) (hK g⁻¹) u
  change ρ g (K.starProjection (u : H)) = (ω g : ℂ) • K.starProjection (u : H)
  rw [← hc, hu, map_smul]

/-- Translation by a norm-one idele class has operator norm at most one. -/
private theorem absolutePWProjection_tendsto_norm (g : C₁) (x : GeoW) :
    ‖hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs (g : C𝔽) x‖ ≤ ‖x‖ := by
  have h1 : ideleClassNorm F (g : C𝔽) = 1 := MonoidHom.mem_ker.mp g.property
  have hlog : Real.log ((((m𝔽) (g : C𝔽)).val : ℝ)) = 0 := by
    rw [show (m𝔽) (g : C𝔽) = 1 from h1]
    simp
  have hb := norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs (g : C𝔽)
  simp only [hlog, neg_zero, zero_mul, mul_zero, Real.exp_zero, max_self, abs_zero,
    add_zero, Real.one_rpow, one_mul] at hb
  exact ((hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs (g : C𝔽)).le_of_opNorm_le hb x).trans_eq
    (one_mul _)

/-- The ambient translation preserves the weighted theta subspace. -/
private theorem absolutePWProjection_tendsto_action (a : ℝ) (g : C𝔽) (x : GeoW)
    (hx : x ∈ globalThetaSobolev F a hGeo hs) :
    hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs g x ∈ globalThetaSobolev F a hGeo hs := by
  obtain ⟨ρ, hρ, -, -⟩ := exists_globalThetaSobolevAction (F := F) a hGeo hs
  have h := (ρ g ⟨x, hx⟩).property
  rw [hρ] at h
  exact h

/-- The geometric projection maps the chosen isotype into itself, because norm-one
translations are unitary and preserve the weighted theta subspace. -/
private theorem absolutePWProjection_tendsto_preservesIsotype (a : ℝ) (ω : PontryaginDual C₁)
    (u : GeoIsotype(ω)) :
    ((ambientGeom(a)).comp (GeoIsotype(ω)).subtypeL) u ∈ GeoIsotype(ω) := by
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs
  let ρ := τ.comp (ideleClassNorm F).ker.subtype
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hK (g : C₁) (x : GeoW) (hx : x ∈ K) : ρ g x ∈ K :=
    absolutePWProjection_tendsto_action (F := F) hs a g x hx
  have hmem := absolutePWProjection_tendsto_isotype GeoW C₁ ρ K hK
    (fun g x ↦ absolutePWProjection_tendsto_norm (F := F) hs g x) ω u
  with_unfolding_all exact hmem

/-- A polar-free homogeneous theta function agrees in the weighted space with the image of
its class under the inclusion of §10.1. -/
private theorem absolutePWProjection_tendsto_theta (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    ∃ u : GeoW, u ∈ globalThetaSobolev F a hGeo hs ∧
      (u : C𝔽 → ℂ) =ᵐ[μ𝔽] globalWeightedTheta(a, ω, f) := by
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo hs ω
  have he := (hj f₀ x rfl).2
  exact ⟨(j x).val.val, (j x).val.property, he⟩

/-- The global absolute levels lie in the weighted theta subspace. -/
private theorem absolutePWProjection_tendsto_le_theta (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ ≤
      (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  obtain ⟨u, hu, he⟩ := absolutePWProjection_tendsto_theta (F := F) (S := S) hs a ω f.val
  have heq : globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val = u := by
    apply Lp.ext
    exact (withDensity_absolutelyContinuous _ _).ae_le
      ((globalPWThetaSobolevMap_apply (F := F) (S := S) (s := s) a ω f.val).trans he.symm)
  change globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val ∈
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW)
  rw [heq]
  exact hu

section AbsoluteLevelDensity

local notation "LocalChar(" ω ", " hω ")" => sLocalNormOneCharacter S ω hω
local notation "LocalH(" η ")" => SLocalHomogeneousThetaSpace F S η
local notation "GlobalH(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "qLocal(" η ")" => (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ
local notation "qGlobal(" ω ")" => (LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)).mkQ
local notation "PolarH(" ω ")" => globalPolarFreeThetaSubmodule (F := F) ω

section

open scoped WithZero

local notation "Cℓ(" v ")" => (v : V).adicCompletion F
local notation "Qℓ(" v ")" => Cℓ(v)ˣ ⧸ ((v : V).adicCompletionIntegers F).units

/-- The relative local presentation of a trivial Picard group clears every finite valuation
outside the original stage by multiplying by the inverse of a single principal idele. -/
private theorem absLevel_idele_unit_outside (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (g : IdeleGroup (𝓞 F) F) :
    ∃ x : Fˣ, ∀ v : V, v ∉ S →
      Valued.v ((g * IdeleGroup.unitEmbedding (𝓞 F) F x⁻¹).val.2 v) = (1 : ℤᵐ⁰) := by
  classical
  have hg : {v : V | Valued.v (g.val.2 v) ≠ (1 : ℤᵐ⁰)}.Finite :=
    eventually_cofinite.mp (AdeleRing.isUnit_iff.mp g.isUnit).2.2
  obtain ⟨T, hT, hPicT⟩ := (picard_uniformization F (S ∪ hg.toFinset)).1
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  let D := T \ S
  let I (v : V) : IdeleGroup (𝓞 F) F →* Cℓ(v)ˣ :=
    Units.map (((RestrictedProduct.evalRingHom (fun w : V ↦ Cℓ(w)) v).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom)
  let u : (v : D) → Qℓ(v.val) := fun v ↦ QuotientGroup.mk (I v.val g)
  obtain ⟨e, -⟩ := (picard_uniformization F S).2.1 T hST hPicT
  have he : (QuotientGroup.mk u : _ ⧸ (sUnitLocalClasses F T D).range) = 1 :=
    e.injective (hPic.elim _ _)
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (N := (sUnitLocalClasses F T D).range) u).mp he
  refine ⟨x.val, fun v hv ↦ ?_⟩
  have hmul : I v (g * IdeleGroup.unitEmbedding (𝓞 F) F x.val⁻¹) =
      I v g * (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val)⁻¹ := by
    rw [map_mul, ← map_inv]
    rfl
  change Valued.v (I v (g * IdeleGroup.unitEmbedding (𝓞 F) F x.val⁻¹)).val = 1
  rw [hmul]
  by_cases hvT : v ∈ T
  · let w : D := ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hv⟩⟩
    have h := congrFun hx w
    change (QuotientGroup.mk (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val) : Qℓ(v)) =
      QuotientGroup.mk (I v g) at h
    have hmem : I v g * (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val)⁻¹ ∈
        (v.adicCompletionIntegers F).units := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (v.adicCompletionIntegers F).units)
        (I v g * (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val)⁻¹) = 1
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr h.symm
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hmem
  · have hg' : Valued.v (g.val.2 v) = (1 : ℤᵐ⁰) := by
      by_contra h
      exact hvT (hT (Finset.mem_union_right _ (hg.mem_toFinset.mpr h)))
    have hx' : Valued.v ((x.val : F) : Cℓ(v)) = (1 : ℤᵐ⁰) := by
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact x.property v hvT
    rw [Units.val_mul, Units.val_inv_eq_inv_val]

    change Valued.v (g.val.2 v * (((x.val : F) : Cℓ(v))⁻¹)) = 1
    rw [map_mul, map_inv₀, hg', hx', inv_one, one_mul]

end

/-- A character unramified outside S is determined by its local restriction when
the S-integer Picard group is trivial. -/
private theorem absLevel_character_eq_one (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial)
    (h : LocalChar(ω, hω) = 1) : ω = 1 := by
  apply PontryaginDual.ext
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.val
  obtain ⟨a, ha⟩ := absLevel_idele_unit_outside S hPic g
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let t := g * d a⁻¹
  have ht : (QuotientGroup.mk t : C𝔽) = x.val := by
    have hd : (QuotientGroup.mk (d a⁻¹) : C𝔽) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a⁻¹, rfl⟩
    change (QuotientGroup.mk' _) (g * d a⁻¹) = x.val
    rw [map_mul]
    change (QuotientGroup.mk g : C𝔽) * QuotientGroup.mk (d a⁻¹) = x.val
    rw [hd, mul_one, hg]
  have htu : t ∈ range (integralIdeleInsertion F S) := by
    apply (mem_range_integralIdeleInsertion F S t).mpr
    intro v hv
    have h1 : t.val.2 v * t.inv.2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 F) F ↦ z.2 v) t.val_inv
    have hval : Valued.v (t.inv.2 v) = 1 := by
      have hvp := congrArg Valued.v h1
      rw [map_mul, ha v hv, one_mul, map_one] at hvp
      exact hvp
    exact ⟨(ha v hv).le, hval.le⟩
  obtain ⟨u, hu⟩ := htu
  let y₀ := Units.map (adeleProjection F S).toMonoidHom t
  have hy : sIdeleQuotientNorm F S (QuotientGroup.mk y₀) = 1 := by
    rw [sIdeleQuotientNorm_mk]
    have hh := (sIdeleNorm_spec F S).1 u
    change ideleNorm F (integralIdeleInsertion F S u) =
      sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u)) at hh
    rw [hu] at hh
    change ideleClassNorm F (QuotientGroup.mk t) = sIdeleNorm F S y₀ at hh
    rw [ht, MonoidHom.mem_ker.mp x.property] at hh
    exact hh.symm
  let y : J₁ := ⟨QuotientGroup.mk y₀, hy⟩
  have hh := sLocalNormOneCharacter_apply ω hω u x y (by rw [hu, ht])
    (by rw [hu])
  rw [h] at hh
  exact hh.symm

/-- The polar-free homogeneous quotient is closed in the unrestricted quotient. -/
private theorem absLevel_isClosed_polar (ω : PontryaginDual C₁) :
    IsClosed (PolarH(ω) : Set (GlobalH(ω))) := by
  by_cases h : ω = 1
  · subst ω
    obtain ⟨R, -, hR, -, -⟩ := globalConverse_normTwist_exact (F := F)
    rw [← hR]
    exact R.isClosed_ker
  · have hsurj := (globalConverse_nontrivial_exact (F := F) ω h).surjective
    have ht : PolarH(ω) = ⊤ := by
      apply Submodule.eq_top_iff'.mpr
      intro x
      obtain ⟨f, hf⟩ := hsurj x
      exact Submodule.mem_map.mpr ⟨f.val, f.property, hf⟩
    rw [ht, Submodule.top_coe]
    exact isClosed_univ

/-- Integer-indicator insertion is surjective on the polar-free homogeneous quotient. -/
private theorem absLevel_exists_local_polar (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial) (x : PolarH(ω)) :
    ∃ f : Zₛ, qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val) = x.val := by
  let η := LocalChar(ω, hω)
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) hPic hω
  let y := e.symm x.val
  have hin (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
      e (qLocal(η) f) = qGlobal(ω) (sAdeleSchwartzToGlobal F S f) :=
    (LinearMap.congr_fun he (qLocal(η) f)).trans (sLocalHomogeneousThetaToGlobal_mk hω f)
  by_cases hw : ω = 1
  · subst ω
    obtain ⟨f, hf⟩ := (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ_surjective y
    have hrep : qGlobal((1 : PontryaginDual C₁)) (sAdeleSchwartzToGlobal F S f) = x.val :=
      (hin f).symm.trans ((congrArg e hf).trans (e.apply_symm_apply x.val))
    obtain ⟨R, hR, hker, -, -⟩ := globalConverse_normTwist_exact (F := F)
    have hx : R x.val = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact x.property
    have hre := hR (sAdeleSchwartzToGlobal F S f)
    rw [hrep, hx] at hre
    let μ := normOneIdeleClassTamagawaMeasure F
    let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
    let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
    have hm : ((μ univ).toReal : ℂ) ≠ 0 := by
      exact_mod_cast (measureReal_univ_pos (μ := μ)).ne'
    have hpol : sAdeleSchwartzToGlobal F S f ∈ adelePolarSubspace F := by
      apply (mem_adelePolarSubspace _).mpr
      exact ⟨(mul_eq_zero.mp (congrArg Prod.fst hre.symm)).resolve_left (neg_ne_zero.mpr hm),
        (mul_eq_zero.mp (congrArg Prod.snd hre.symm)).resolve_left hm⟩
    exact ⟨⟨f, (mem_sAdelePolarSubspace f).mpr
      ((sAdeleSchwartzToGlobal_mem_polarSubspace_iff S f).mp hpol)⟩, hrep⟩
  · have hη : η ≠ 1 := fun h ↦ hw (absLevel_character_eq_one ω hω hPic h)
    have hy : y ∈ (sAdelePolarSubspace F S).map (qLocal(η)) := by
      rw [sLocalZeroMomentTheta_eq_top η hη]
      exact Submodule.mem_top
    obtain ⟨f, hf, hq⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨f, hf⟩, (hin f).symm.trans ((congrArg e hq).trans (e.apply_symm_apply x.val))⟩

/-- An action on a submodule has the ambient isotype whenever its inclusion
intertwines the two actions. -/
private theorem absLevel_mem_isotype_of_submodule {W G : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [Group G] [TopologicalSpace G]
    (K : Submodule ℂ W) (ρ : G →* (K →L[ℂ] K)) (σ : G →* (W →L[ℂ] W))
    (hρ : ∀ g u, (ρ g u).val = σ g u.val) (ω : PontryaginDual G) (u : K) :
    u ∈ actionIsotype ρ ω ↔ u.val ∈ actionIsotype σ ω := by
  constructor
  · intro h
    apply (mem_actionIsotype σ ω u.val).mpr
    intro g
    exact (hρ g u).symm.trans
      (congrArg Subtype.val ((mem_actionIsotype ρ ω u).mp h g))
  · intro h
    apply (mem_actionIsotype ρ ω u).mpr
    intro g
    exact Subtype.ext ((hρ g u).trans ((mem_actionIsotype σ ω u.val).mp h g))

/-- The isotype action inside the theta subspace agrees with the ambient action. -/
private theorem absLevel_isotype_agree (a : ℝ) (ω : PontryaginDual C₁)
    (u : globalThetaSobolev F a hGeo hs) :
    u ∈ actionIsotype ((exists_globalThetaSobolevAction (F := F) a hGeo hs).choose.comp
      (ideleClassNorm F).ker.subtype) ω ↔ u.val ∈ GeoIsotype(ω) :=
  absLevel_mem_isotype_of_submodule _ _ _
    (fun g u ↦ (exists_globalThetaSobolevAction (F := F) a hGeo hs).choose_spec.1 g.val u) ω u

/-- Use the closed preimage of the desired Sobolev subspace to pass first through
each level closure and then through the sequentially dense union. -/
private theorem absLevel_dense_polar_image (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial)
    {Y : Type*} [TopologicalSpace Y] (J : PolarH(ω) → Y) (hJ : Continuous J)
    (C : Set Y) (hC : IsClosed C)
    (hgen : ∀ (f : Zₛ) (Λ : ℝ)
      (_hf : f.val ∈ sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ)),
      J ⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val),
        Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace f, rfl⟩⟩ ∈ C) :
    ∀ x : PolarH(ω), J x ∈ C := by
  classical
  let η := LocalChar(ω, hω)
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) hPic hω
  let D := e ⁻¹' ((Subtype.val : PolarH(ω) → GlobalH(ω)) '' (J ⁻¹' C))
  have hD : IsClosed D :=
    ((absLevel_isClosed_polar ω).isClosedEmbedding_subtypeVal.isClosedMap _
      (hC.preimage hJ)).preimage e.continuous
  have hlevel (Λ : ℝ) :
      (sLocalAbsolutePW (F := F) (S := S) (T := S) le_rfl Λ (sAdelePolarSubspace F S) η :
        Set (LocalH(η))) ⊆ D := by
    change _ ⊆ D
    rw [sLocalAbsolutePW, Submodule.topologicalClosure_coe]
    apply closure_minimal _ hD
    rintro z ⟨f, hf, rfl⟩
    refine ⟨⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f),
      Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace
        (⟨f, hf.2⟩ : Zₛ), rfl⟩⟩, hgen ⟨f, hf.2⟩ Λ hf.1, ?_⟩
    exact ((LinearMap.congr_fun he (qLocal(η) f)).trans
      (sLocalHomogeneousThetaToGlobal_mk hω f)).symm
  intro x
  obtain ⟨f, hrep⟩ := absLevel_exists_local_polar ω hω hPic x
  have hseq := sLocalAbsolutePW_seqDense (F := F) (S := S) (T := S) (S₀ := ∅)
    le_rfl (Finset.union_empty S).symm (Finset.disjoint_empty_right S) isSaturatedPlaceSet_empty
    hPic ω hω η rfl (sAdelePolarSubspace F S) (Or.inr rfl) (qLocal(η) f.val)
    (Submodule.mem_map_of_mem f.property)
  obtain ⟨u, hu, hlim⟩ := hseq
  have hz : qLocal(η) f.val ∈ D := hD.mem_of_tendsto hlim (.of_forall fun n ↦ by
    obtain ⟨Λ, -, hΛ⟩ := hu n
    exact hlevel Λ hΛ)
  obtain ⟨z, hz, hz'⟩ := hz
  have heq : e (qLocal(η) f.val) = x.val :=
    ((LinearMap.congr_fun he (qLocal(η) f.val)).trans
      (sLocalHomogeneousThetaToGlobal_mk hω f.val)).trans hrep
  rwa [show z = x from Subtype.ext (hz'.trans heq)] at hz

/-- A dense family in a submodule is dense in its image under inclusion. -/
private theorem absLevel_dense_submodule_inclusion {W X : Type*}
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [TopologicalSpace X]
    (I K : Submodule ℂ W) (H : Submodule ℂ K)
    (hH : ∀ u : K, u ∈ H ↔ u.val ∈ I) (j : X → H)
    (hj : Continuous j) (hjd : DenseRange j) :
    ∃ J : X → I, Continuous J ∧ (∀ x, (J x).val = (j x).val.val) ∧
      ∀ (C : Set I), IsClosed C → (∀ x, J x ∈ C) → ∀ u : I, u.val ∈ K → u ∈ C := by
  let i (u : H) : I := ⟨u.val.val, (hH u.val).mp u.property⟩
  have hi : Continuous i :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  refine ⟨i ∘ j, hi.comp hj, fun x ↦ rfl, fun C hC hd u hu ↦ ?_⟩
  let v : H := ⟨⟨u.val, hu⟩, (hH ⟨u.val, hu⟩).mpr u.property⟩
  have hc : IsClosed (i ⁻¹' C) := hC.preimage hi
  have hv : i v ∈ C := hc.closure_subset_iff.mpr (Set.range_subset_iff.mpr hd) (hjd v)
  exact hv

/-- The dense homogeneous inclusion, viewed in the ambient isotype, agrees with
the level generator on every inserted polar-free test. -/
private theorem absLevel_exists_sobolev_image (a : ℝ) (ω : PontryaginDual C₁) :
    let I : Submodule ℂ GeoW := GeoIsotype(ω)
    let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
    ∃ J : PolarH(ω) → I, Continuous J ∧
      (∀ f : Zₛ, (J ⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val),
        Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace f, rfl⟩⟩).val =
          globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f) ∧
      ∀ (C : Set I), IsClosed C → (∀ x, J x ∈ C) →
        ∀ u : I, u.val ∈ K → u ∈ C := by
  intro I K
  let hInc := exists_globalHomogeneousThetaSobolevInclusion (F := F)
    (a := a) (α := -(0 : ℝ)) (β := 0) (s := s) hGeo hs ω
  let j := hInc.choose
  have hjd := hInc.choose_spec.2.1
  have hj := hInc.choose_spec.2.2
  let ρ := (exists_globalThetaSobolevAction (F := F) a hGeo hs).choose.comp
    (ideleClassNorm F).ker.subtype
  let H : Submodule ℂ K := actionIsotype ρ ω
  have hH (u : K) : u ∈ H ↔ u.val ∈ I := absLevel_isotype_agree (F := F) hs a ω u
  obtain ⟨J, hJ, hJv, hJd⟩ := absLevel_dense_submodule_inclusion I K H hH j j.continuous hjd
  refine ⟨J, hJ, fun f ↦ ?_, hJd⟩
  let F₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
  let x : PolarH(ω) := ⟨qGlobal(ω) F₀.val, Submodule.mem_map.mpr ⟨_, F₀.property, rfl⟩⟩
  change (J x).val = _
  refine (hJv x).trans ?_
  apply Lp.ext
  exact (withDensity_absolutelyContinuous _ _).ae_le
    ((hj F₀ x rfl).2.trans (globalPWThetaSobolevMap_apply (s := s) a ω f).symm)

private theorem absLevel_density (a : ℝ) (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial) :
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW).comap (GeoIsotype(ω)).subtype ≤
      (⨆ Λ : ℝ, absLevel(a, ω, Λ)).topologicalClosure := by
  let hImage := absLevel_exists_sobolev_image (F := F) (S := S) hs a ω
  let J := hImage.choose
  have hJ := hImage.choose_spec.1
  have hJv := hImage.choose_spec.2.1
  have hJd := hImage.choose_spec.2.2
  let C : Submodule ℂ GeoIsotype(ω) := (⨆ Λ : ℝ, absLevel(a, ω, Λ)).topologicalClosure
  have hC : IsClosed (C : Set GeoIsotype(ω)) := Submodule.isClosed_topologicalClosure _
  have hd : ∀ x : PolarH(ω), J x ∈ C := by
    apply absLevel_dense_polar_image ω hω hPic J hJ (C : Set GeoIsotype(ω)) hC
    intro f Λ hf
    let x : PolarH(ω) := ⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val),
      Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace f, rfl⟩⟩
    have hmem : J x ∈ absLevel(a, ω, Λ) := by
      change (J x).val ∈ globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ
      have he := hJv f
      change (J x).val = _ at he
      rw [he]
      exact globalAbsolutePWSobolev_mem hs a ω Λ f hf
    exact Submodule.le_topologicalClosure _ ((le_iSup (fun r ↦ absLevel(a, ω, r)) Λ) hmem)
  intro u hu
  exact hJd (C : Set GeoIsotype(ω)) hC hd u hu

end AbsoluteLevelDensity

/-- Paper: Theorem 11.2.1.2(1) and Proposition 7.3.2.2(1), pp. 352, 488.
Every vector of the isotype lying in the weighted theta subspace is a limit of vectors
of the absolute levels.
Deviation: Use X = Λ and the direct integer-indicator insertion. The printed density of
Proposition 7.3.2.2(1) uses unit insertion and is refuted (ERRATA F123). -/
theorem globalThetaSobolev_isotype_le_closure_absLevel (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) :
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW).comap (GeoIsotype(ω)).subtype ≤
      (⨆ Λ : ℝ, absLevel(a, ω, Λ)).topologicalClosure :=
  absLevel_density (F := F) (S := S) hs a ω _hω _hPic

/-- Paper: Theorem 11.2.1.2(1), p. 488.
The absolute projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem absolutePWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ absolutePWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) := by
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := absLevel(a, ω, Λ)
  haveI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  haveI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hmono : Monotone levels := fun _ _ h ↦
    Submodule.comap_mono (absolutePWProjection_tendsto_mono (F := F) (S := S) hs a ω h)
  have hK (v : I) : K.starProjection (v : GeoW) ∈ I :=
    absolutePWProjection_tendsto_preservesIsotype (F := F) hs a ω v
  have hle (Λ : ℝ) : levels Λ ≤ K.comap I.subtype := fun _ hw ↦
    absolutePWProjection_tendsto_le_theta (F := F) (S := S) hs a ω Λ hw
  have hdense : K.comap I.subtype ≤ (⨆ Λ, levels Λ).topologicalClosure :=
    globalThetaSobolev_isotype_le_closure_absLevel (F := F) (S := S) hs a ω _hω _hPic
  with_unfolding_all exact absolutePWProjection_tendsto_limit GeoW I K levels hmono hK hle hdense u

variable {R ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

local notation "cutoffConv(" a ", " ω ", " hρ ", " φ ")" =>
  onIsotype(ω, geometricTruncatedConvolution (F := F) a h₀ hs hρ φ)
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

-- At a fixed cutoff the uncompressed operator may have a different trace.
-- On theta inputs Q A Q = A Q, so cutoff condensation only needs the
-- trace class of Mρ A Q. Cutoff convolution Mρ A is already trace class
-- by §9.3.3 (a larger smooth cutoff can be chosen to cover tsupport ρ).

/-- Every cutoff is absorbed by a larger cutoff satisfying the inner-band condition. -/
private theorem exists_nuclear_geometricPWRestriction_cover
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (R ε : ℝ) (ρ : G → ℝ) (hρ : IsModulatedCutoff m R ε ρ) :
    ∃ (L d : ℝ) (χ : G → ℝ), IsModulatedCutoff m L d χ ∧
      (0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) ∧ ∀ x, ρ x * χ x = ρ x := by
  let L := R + 2
  let d := L⁻¹ / 4
  have hL : 2 < L := by dsimp [L]; linarith [hρ.radius_pos]
  have hLp : 0 < L := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hdlt : d < L⁻¹ := by dsimp [d]; nlinarith [inv_pos.mpr hLp]
  have hinv : L⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hdsmall : d < 1 / 2 := by dsimp [d]; linarith
  have hplateau : 1 < L - d := by linarith
  have hprod : 1 ≤ (L⁻¹ + d) * (L - d) := by
    have hh := mul_nonneg hd.le (show 0 ≤ L - L⁻¹ - d by linarith)
    nlinarith [inv_mul_cancel₀ hLp.ne']
  let B : ContDiffBump (0 : ℝ) :=
    ⟨Real.log (L - d), Real.log L, Real.log_pos hplateau,
      Real.log_lt_log (by linarith) (by linarith)⟩
  let r (x : G) : ℝ := (m x).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let χ (x : G) := B (Real.log (r x))
  have h1 : χ 1 = 1 := by
    apply B.one_of_mem_closedBall
    simp [r, B.rIn_pos.le]
  have hcut : IsModulatedCutoff m L d χ := by
    refine ⟨hLp, hd, by linarith, by linarith, fun _ ↦ B.nonneg,
      fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact IsGreatest.csSup_eq ⟨⟨1, h1⟩, forall_mem_range.mpr fun _ ↦ B.le_one⟩
    · refine ⟨fun t ↦ B (Real.log t), ∅, fun _ ↦ rfl, by simp, ?_, by simp⟩
      simp only [Finset.coe_empty, sdiff_empty]
      exact B.contDiff.comp_contDiffOn (fun x hx ↦ (Real.contDiffAt_log.mpr (mem_Ioi.mp hx).ne').contDiffWithinAt)
    · intro x
      change B (Real.log ((m x).val : ℝ)) = B (Real.log ((m x⁻¹).val : ℝ))
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, B.neg]
    · apply closure_minimal _ (isClosed_Icc.preimage hr)
      intro x hx
      have hmem : Real.log (r x) ∈ support B := hx
      rw [B.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
      obtain ⟨hl, hu⟩ := abs_lt.mp hmem
      change L⁻¹ ≤ r x ∧ r x ≤ L
      rw [← Real.log_le_log_iff (inv_pos.mpr hLp) (hpos x), Real.log_inv,
        ← Real.log_le_log_iff (hpos x) hLp]
      exact ⟨hl.le, hu.le⟩
    · intro x hx
      apply B.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      change -Real.log (L - d) ≤ _ ∧ _ ≤ Real.log (L - d)
      rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr (by linarith)) (hpos x),
        Real.log_le_log_iff (hpos x) (by linarith)]
      change L⁻¹ + d ≤ r x ∧ r x ≤ L - d at hx
      exact ⟨((inv_le_iff_one_le_mul₀ (by linarith : 0 < L - d)).mpr hprod).trans hx.1, hx.2⟩
  refine ⟨L, d, χ, hcut, ⟨by positivity, by linarith⟩, ?_⟩
  intro x
  by_cases hx : ρ x = 0
  · simp [hx]
  have hband := hρ.support_subset (subset_tsupport ρ (mem_support.mpr hx))
  have hR : R ≤ L - d := by dsimp [L] at *; linarith
  have hχ : χ x = 1 := by
    apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    change -Real.log (L - d) ≤ _ ∧ _ ≤ Real.log (L - d)
    rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr (by linarith)) (hpos x),
      Real.log_le_log_iff (hpos x) (by linarith)]
    exact ⟨(inv_anti₀ hρ.radius_pos hR).trans hband.1, hband.2.trans hR⟩
  rw [hχ, mul_one]
/-- Pointwise absorption of cutoff symbols gives absorption of their L² multipliers. -/
private theorem exists_nuclear_geometricPWRestriction_absorb
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (ν : Measure G) (R ε L d : ℝ) (ρ χ : G → ℝ)
    (hρ : IsModulatedCutoff m R ε ρ) (hχ : IsModulatedCutoff m L d χ)
    (hprod : ∀ x, ρ x * χ x = ρ x) :
    (modulatedCutoffOperator m ν hρ).comp (modulatedCutoffOperator m ν hχ) =
      modulatedCutoffOperator m ν hρ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [modulatedCutoffOperator_apply m ν hρ (modulatedCutoffOperator m ν hχ u),
    modulatedCutoffOperator_apply m ν hχ u, modulatedCutoffOperator_apply m ν hρ u] with x hx hx' hy
  change modulatedCutoffOperator m ν hρ (modulatedCutoffOperator m ν hχ u) x = modulatedCutoffOperator m ν hρ u x
  rw [hx, hx', hy, ← mul_assoc, ← Complex.ofReal_mul, hprod]
/-- An admissible cutoff followed by Hardy–Sobolev convolution is nuclear. -/
private theorem exists_nuclear_geometricPWRestriction_admissible
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) (φ : BruhatCompactSupport G)
    (L d : ℝ) (χ : G → ℝ) (hχ : IsModulatedCutoff m L d χ)
    (hband : 0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) :
    IsNuclearOperator ((modulatedCutoffOperator m
      (μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))) hχ).comp
      (hardySobolevTestAction μ m a b s hab hs φ)) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  obtain ⟨hbig, _, _⟩ := truncatedHardySobolevConvolution_trace μ m a b s hab hs φ.val
    hc.aemeasurable φ.property.2 hb hm hms hφs hχ hband
  have hconv := hardySobolevConvolution_eq_testAction μ m a b s hab hs φ hc.aemeasurable hb
  exact (congrArg (fun U ↦ IsNuclearOperator ((modulatedCutoffOperator m
      (μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))) hχ).comp U)) hconv).mp hbig

/-- Bounded precomposition and postcomposition preserve nuclearity between Hilbert spaces. -/
private theorem exists_nuclear_geometricPWRestriction_compress
    (H J : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (S : J →L[ℂ] H) (R : H →L[ℂ] J) :
    IsNuclearOperator (R.comp (A.comp S)) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
  let pre := (ContinuousLinearMap.compL ℂ J H ℂ).flip S
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, (fun n ↦ (φ n).comp S), R ∘ y, hc, ?_, ?_, ?_⟩
  · exact (pre.continuous.tendsto' 0 0 (map_zero pre)).comp hφ
  · exact (R.continuous.tendsto' 0 0 (map_zero R)).comp hy
  · intro x
    simpa only [map_smul, Function.comp_apply, ContinuousLinearMap.comp_apply] using R.hasSum (hsum (S x))
/-- A vector fixed by a compressed orthogonal projector is fixed by the ambient projector. -/
private theorem exists_nuclear_geometricPWRestriction_fixed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K] (u : I)
    (hu : I.orthogonalProjectionOnto (K.starProjection (u : H)) = u) :
    K.starProjection (u : H) = u := by
  have hi := congrArg (fun v : I ↦ RCLike.re (inner ℂ v u)) hu
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    K.re_inner_starProjection_eq_normSq] at hi
  have hnorm : ‖K.starProjection (u : H)‖ = ‖(u : H)‖ := by
    have hs : ‖K.starProjection (u : H)‖ ^ 2 = ‖(u : H)‖ ^ 2 := by
      simpa only [Submodule.starProjection_apply, Submodule.norm_coe, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using hi
    nlinarith [norm_nonneg (K.starProjection (u : H)), norm_nonneg (u : H)]
  exact K.starProjection_eq_self_iff.mpr ((K.mem_iff_norm_starProjection (u : H)).mpr hnorm)
/-- The two cutoff composition orders agree on inputs fixed by the compressed geometric projector. -/
private theorem exists_nuclear_geometricPWRestriction_agree
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (M A : H →L[ℂ] H)
    (hAK : K.starProjection.comp (A.comp K.starProjection) = A.comp K.starProjection)
    (P : I →L[ℂ] I)
    (hP : (I.orthogonalProjectionOnto.comp (K.starProjection.comp I.subtypeL)) * P = P) :
    (I.orthogonalProjectionOnto.comp (M.comp (A.comp (K.starProjection.comp I.subtypeL)))) * P =
      (I.orthogonalProjectionOnto.comp (M.comp (K.starProjection.comp (A.comp I.subtypeL)))) * P := by
  apply ContinuousLinearMap.ext
  intro u
  have hfix := congrArg (fun U : I →L[ℂ] I ↦ U u) hP
  have hp : K.starProjection (P u : H) = P u := exists_nuclear_geometricPWRestriction_fixed H I K (P u) hfix
  have ha := congrArg (fun U : H →L[ℂ] H ↦ U (P u)) hAK
  change K.starProjection (A (K.starProjection (P u : H))) = A (K.starProjection (P u : H)) at ha
  rw [hp] at ha
  change I.orthogonalProjectionOnto (M (A (K.starProjection (P u : H)))) = I.orthogonalProjectionOnto (M (K.starProjection (A (P u : H))))
  rw [hp, ha]


/-- Paper: Theorems 11.2.1.2(2) and 11.2.1.4(2), pp. 488–489.
The cutoff geometric restriction is trace class on the chosen isotype.
It agrees with cutoff geometric convolution after any map into theta.
Deviation: Use the right-compressed operator for the corrected limits. -/
theorem exists_nuclear_geometricPWRestriction (a : ℝ) (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    ∃ T : nuclearEndomorphisms GeoIsotype(ω),
      T.val = onIsotype(ω, geometricRestriction (F := F) a h₀ hs hρ φ) ∧
      ∀ P : GeoIsotype(ω) →L[ℂ] GeoIsotype(ω), Pgeom(a, ω) * P = P →
        T.val * P = cutoffConv(a, ω, hρ, φ) * P := by
  have hcover : ∃ (L d : ℝ) (χ : C𝔽 → ℝ), IsModulatedCutoff m𝔽 L d χ ∧
      (0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) ∧ ∀ x, ρ x * χ x = ρ x := by
    with_unfolding_all exact exists_nuclear_geometricPWRestriction_cover C𝔽 m𝔽 R ε ρ hρ
  obtain ⟨L, d, χ, hχ, hband, hprod⟩ := hcover
  let H := GeoW
  let I : Submodule ℂ H := GeoIsotype(ω)
  let K : Submodule ℂ H := globalThetaSobolev F a hGeo hs
  let M : H →L[ℂ] H := by with_unfolding_all exact modulatedCutoffOperator m𝔽 globalWMeasure hρ
  let A : H →L[ℂ] H := by with_unfolding_all exact geoAction(φ)
  letI : CompleteSpace I := by with_unfolding_all exact (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  let N : H →L[ℂ] H := by with_unfolding_all exact modulatedCutoffOperator m𝔽 globalWMeasure hχ
  have hn : IsNuclearOperator (N.comp A) := by
    with_unfolding_all
      exact exists_nuclear_geometricPWRestriction_admissible C𝔽 μ𝔽 m𝔽
        ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1 (-(0 : ℝ)) 0 s hGeo hs φ L d χ hχ hband
  have habsorb : M.comp N = M := exists_nuclear_geometricPWRestriction_absorb C𝔽 m𝔽 globalWMeasure R ε L d ρ χ hρ hχ hprod
  have hsmall : IsNuclearOperator (M.comp A) := by
    have hh := mul_mem_nuclearEndomorphisms_left M (⟨N.comp A, hn⟩ : nuclearEndomorphisms H)
    change IsNuclearOperator (M.comp (N.comp A)) at hh
    rwa [← ContinuousLinearMap.comp_assoc, habsorb] at hh
  let U : H →L[ℂ] H := M.comp (A.comp K.starProjection)
  have hU : IsNuclearOperator U := mul_mem_nuclearEndomorphisms_right K.starProjection
    (⟨M.comp A, hsmall⟩ : nuclearEndomorphisms H)
  have hnI := exists_nuclear_geometricPWRestriction_compress H I U hU I.subtypeL I.orthogonalProjectionOnto
  let T : nuclearEndomorphisms I := ⟨I.orthogonalProjectionOnto.comp (U.comp I.subtypeL), hnI⟩
  refine ⟨T, ?_, ?_⟩
  · with_unfolding_all rfl
  · intro P hP
    have hAK : K.starProjection.comp (A.comp K.starProjection) = A.comp K.starProjection := by
      with_unfolding_all exact geometricProjection_convolution_geometricProjection (F := F) a h₀ hs φ
    with_unfolding_all exact exists_nuclear_geometricPWRestriction_agree H I K M A hAK P hP

local notation "nuclearRestriction(" a ", " ω ", " hρ ", " φ ")" =>
  (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose

/-- Uniformly bounded self-adjoint strongly null families kill nuclear operators on the right in trace norm. -/
private theorem absolutePWCondensation_traceNorm_tendsto_null
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : ℝ → H →L[ℂ] H) (hQ : ∀ x, Tendsto (fun i ↦ Q i x) atTop (𝓝 0))
    (hQa : ∀ i, (Q i).adjoint = Q i) (hQc : ∀ i x, ‖Q i x‖ ≤ 2 * ‖x‖)
    (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm ⟨T.val * Q i, mul_mem_nuclearEndomorphisms_right (Q i) T⟩)
      atTop (𝓝 0) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hT⟩ := (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  let u (n : ℕ) := (InnerProductSpace.toDual ℂ H).symm (φ n)
  have hu (n : ℕ) : ‖u n‖ = ‖φ n‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map _
  let cost (i : ℝ) (n : ℕ) := ‖c n‖ * (‖Q i (u n)‖ * ‖y n‖)
  let bound (n : ℕ) := 2 * (‖c n‖ * (‖φ n‖ * ‖y n‖))
  have hcost_nonneg (i : ℝ) (n : ℕ) : 0 ≤ cost i n := by dsimp [cost]; positivity
  have hbound (i : ℝ) (n : ℕ) : ‖cost i n‖ ≤ bound n := by
    rw [Real.norm_of_nonneg (hcost_nonneg i n)]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ((hQc i (u n)).trans_eq (congrArg (2 * ·) (hu n))) (norm_nonneg (y n)))
      (norm_nonneg (c n))
    dsimp only [cost, bound]
    nlinarith
  have hs : Summable bound := by
    obtain ⟨C, hC, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
    obtain ⟨D, _, hyD⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
    apply Summable.mul_left 2
    refine (hc.mul_right (C * D)).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hφC _ (mem_range_self n)) (hyD _ (mem_range_self n))
        (norm_nonneg _) hC.le) (norm_nonneg _)
  have hlim : Tendsto (fun i ↦ ∑' n, cost i n) atTop (𝓝 0) := by
    have hterm (n : ℕ) : Tendsto (fun i ↦ cost i n) atTop (𝓝 0) := by
      simpa [cost] using ((hQ (u n)).norm.mul_const ‖y n‖).const_mul ‖c n‖
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hs hterm (Eventually.of_forall hbound)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  refine squeeze_zero (fun _ ↦ (traceNorm_normedSpaceCore (H := H)).toCore.norm_nonneg _)
    ?_ hlim
  intro i
  let ψ (n : ℕ) : StrongDual ℂ H := c n • innerSL ℂ (Q i (u n))
  have hψ (n : ℕ) : ‖ψ n‖ * ‖y n‖ = cost i n := by
    simp only [ψ, cost, norm_smul, innerSL_apply_norm, mul_assoc]
  simp_rw [← hψ]
  refine traceNorm_le_of_rankOne_series _ ψ y
    ((hs.of_norm_bounded (hbound i)).congr fun n ↦ (hψ n).symm) fun x ↦ ?_
  have heval (n : ℕ) : ψ n x = c n * φ n (Q i x) := by
    have hinner := (Q i).adjoint_inner_left x (u n)
    rw [hQa] at hinner
    simp only [ψ, smul_apply, smul_eq_mul, innerSL_apply_apply, hinner, u, InnerProductSpace.toDual_symm_apply]
  simpa [heval, mul_apply_eq_comp] using hT (Q i x)
/-- A compressed ambient projection preserves the compressing subspace if it is a strong limit of orthogonal projections. -/
private theorem absolutePWCondensation_traceNorm_tendsto_preserves
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u)))) (u : I) :
    K.starProjection u ∈ I := by
  let w := K.starProjection (u : H)
  let z := I.orthogonalProjectionOnto w
  have hiC : Tendsto (fun i ↦ inner ℂ ((levels i).starProjection u) u) atTop (𝓝 (inner ℂ z u)) :=
    (hlim u).inner tendsto_const_nhds
  have hi := (RCLike.continuous_re.tendsto _).comp hiC
  have heq (i : ℝ) : RCLike.re (inner ℂ ((levels i).starProjection u) u) = ‖(levels i).starProjection u‖ ^ 2 := by
    with_unfolding_all simpa only [Submodule.starProjection_apply, Submodule.norm_coe] using (levels i).re_inner_starProjection_eq_normSq u
  have hn : Tendsto (fun i ↦ RCLike.re (inner ℂ ((levels i).starProjection u) u)) atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa only [heq] using (hlim u).norm.pow 2
  have hz : RCLike.re (inner ℂ z u) = ‖z‖ ^ 2 := tendsto_nhds_unique hi hn
  have hw : RCLike.re (inner ℂ w (u : H)) = ‖w‖ ^ 2 := by
    with_unfolding_all simpa only [w, Submodule.starProjection_apply, Submodule.norm_coe] using K.re_inner_starProjection_eq_normSq (u : H)
  have hnorm : ‖I.starProjection w‖ = ‖w‖ := by
    have hh : RCLike.re (inner ℂ z u) = RCLike.re (inner ℂ w (u : H)) := by
      rw [show z = I.orthogonalProjectionOnto w from rfl, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    have hsq : ‖I.starProjection w‖ ^ 2 = ‖w‖ ^ 2 := by
      change ‖z‖ ^ 2 = ‖w‖ ^ 2
      linarith
    nlinarith [norm_nonneg (I.starProjection w), norm_nonneg w]
  exact (I.mem_iff_norm_starProjection w).mpr hnorm
/-- Strong convergence of orthogonal projections preserves a right-supported nuclear operator in trace norm. -/
private theorem absolutePWCondensation_traceNorm_tendsto_projection
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (levels : ℝ → Submodule ℂ H) [∀ i, CompleteSpace (levels i)] (R : H →L[ℂ] H)
    (hlim : ∀ u, Tendsto (fun i ↦ (levels i).starProjection u) atTop (𝓝 (R u)))
    (T : nuclearEndomorphisms H) (hTR : T.val * R = T.val) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * (levels i).starProjection, mul_mem_nuclearEndomorphisms_right (levels i).starProjection T⟩ - T))
      atTop (𝓝 0) := by
  have hRa : R.adjoint = R := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hl : Tendsto (fun i ↦ inner ℂ x ((levels i).starProjection y)) atTop (𝓝 (inner ℂ x (R y))) := tendsto_const_nhds.inner (hlim y)
    have hr : Tendsto (fun i ↦ inner ℂ ((levels i).starProjection x) y) atTop (𝓝 (inner ℂ (R x) y)) := (hlim x).inner tendsto_const_nhds
    have heq : (fun i ↦ inner ℂ x ((levels i).starProjection y)) = (fun i ↦ inner ℂ ((levels i).starProjection x) y) := by
      funext i
      exact (Submodule.inner_starProjection_left_eq_right (levels i) x y).symm
    rw [heq] at hl
    exact tendsto_nhds_unique hl hr
  have hR (x : H) : ‖R x‖ ≤ ‖x‖ :=
    le_of_tendsto' ((hlim x).norm) (fun i ↦ (levels i).norm_starProjection_apply_le x)
  let Q (i : ℝ) := (levels i).starProjection - R
  have hQ (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    simpa [Q] using (hlim x).sub (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ R x) atTop (𝓝 (R x)))
  have hQa (i : ℝ) : (Q i).adjoint = Q i := by
    simp only [Q, map_sub, (isSelfAdjoint_starProjection (levels i)).adjoint_eq, hRa]
  have hQc (i : ℝ) (x : H) : ‖Q i x‖ ≤ 2 * ‖x‖ := by
    exact (norm_sub_le ((levels i).starProjection x) (R x)).trans (by linarith [(levels i).norm_starProjection_apply_le x, hR x])
  have hh := absolutePWCondensation_traceNorm_tendsto_null H Q hQ hQa hQc T
  apply hh.congr'
  filter_upwards with i
  apply congrArg traceNorm
  apply Subtype.ext
  change T.val * ((levels i).starProjection - R) = T.val * (levels i).starProjection - T.val
  rw [mul_sub, hTR]
/-- The right-compressed nuclear operator is recovered by strongly convergent compressed projections. -/
private theorem absolutePWCondensation_traceNorm_tendsto_compressed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (A : H →L[ℂ] H) (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))))
    (T : nuclearEndomorphisms I)
    (hTval : T.val = I.orthogonalProjectionOnto.comp (A.comp (K.starProjection.comp I.subtypeL))) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * (levels i).starProjection, mul_mem_nuclearEndomorphisms_right (levels i).starProjection T⟩ - T))
      atTop (𝓝 0) := by
  let R : I →L[ℂ] I := I.orthogonalProjectionOnto.comp (K.starProjection.comp I.subtypeL)
  apply absolutePWCondensation_traceNorm_tendsto_projection I levels R hlim T
  rw [hTval]
  apply ContinuousLinearMap.ext
  intro u
  change I.orthogonalProjectionOnto (A (K.starProjection (I.starProjection (K.starProjection (u : H))))) = I.orthogonalProjectionOnto (A (K.starProjection (u : H)))
  rw [I.starProjection_eq_self_iff.mpr (absolutePWCondensation_traceNorm_tendsto_preserves H I K levels hlim u),
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem (u : H))]


/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
Right multiplication of cutoff geometric convolution by the absolute projections
converges in trace norm.
Deviation: For the fixed cutoff keep the right geometric projection in the
limit. Use the trace class of cutoff convolution on the geometric range. -/
theorem absolutePWCondensation_traceNorm_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ traceNorm
      (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ) -
        T)) atTop (𝓝 0) := by
  intro T
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := (globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ).comap I.subtype
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hlim (u : I) : Tendsto (fun Λ ↦ (levels Λ).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
    with_unfolding_all exact absolutePWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic u
  have hTval : T.val = I.orthogonalProjectionOnto.comp
      (((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))).comp (K.starProjection.comp I.subtypeL)) := by
    with_unfolding_all exact (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose_spec.1
  with_unfolding_all
    exact absolutePWCondensation_traceNorm_tendsto_compressed GeoW I K
      ((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))) levels hlim T hTval

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
The traces of the cutoff absolute condensations converge to the trace of the
cutoff operator composed on the right with the geometric projection.
Deviation: Keep the right geometric projection at the fixed cutoff. -/
theorem absolutePWCondensation_trace_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ hilbertTrace
      (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ))) atTop
      (𝓝 (hilbertTrace T)) := by
  have limit {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : nuclearEndomorphisms H) (A : ℝ → nuclearEndomorphisms H)
      (h : Tendsto (fun r ↦ traceNorm (A r - T)) atTop (𝓝 0)) :
      Tendsto (fun r ↦ hilbertTrace (A r)) atTop (𝓝 (hilbertTrace T)) := by
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub]
    simp only [htr]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _) h
  let T := nuclearRestriction(a, ω, hρ, φ)
  exact limit (H := ↥(GeoIsotype(ω))) T
    (fun r ↦ productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω r))
    (absolutePWCondensation_traceNorm_tendsto (F := F) (S := S) hs a ω _hω _hPic φ _hφ hρ)

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488.
The local invariant level completes the weighted theta image of zero-moment
tests with compact Fourier support in the product-norm region of size Λ.
Deviation: Use a positive local twist so the weighted theta functions belong to L². -/
def sLocalInvariantPWSobolev (_hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) :
    Submodule ℂ LocalW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWProductRegion S Λ) ↦
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488.
A polar-free test band-limited by product norm gives its weighted homogeneous
theta vector in the local invariant level.
Deviation: Use the positive local twist of the repaired definition. -/
theorem sLocalInvariantPWSobolev_mem {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWProductRegion S Λ)) :
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.7), p. 488.
The global invariant level completes the weighted homogeneous theta image
of the inserted polar-free tests with compact Fourier support in the product region.
Deviation: Use the integer-indicator insertion of §7.3.2 directly from S. -/
def globalInvariantPWSobolev (_hs : 0 ≤ s) (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    Submodule ℂ GeoW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWProductRegion S Λ) ↦
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.7), p. 488.
An inserted polar-free test band-limited by product norm gives its weighted
homogeneous theta vector in the global invariant level.
Deviation: Use the direct integer-indicator insertion. -/
theorem globalInvariantPWSobolev_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWProductRegion S Λ)) :
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

local notation "invLevel(" a ", " ω ", " Λ ")" =>
  (globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ).comap (GeoIsotype(ω)).subtype

/-- Paper: Definition 11.2.1.3(2) and (11.2.1.8), p. 489.
The invariant truncation is the orthogonal projection onto the global invariant level.
Deviation: Include the projected vector back into the ambient isotype. -/
def invariantPWProjection (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  letI : IsClosed (invLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  (invLevel(a, ω, Λ)).starProjection

/-- Paper: Definition 11.2.1.3(2), p. 489.
The invariant projection fixes vectors in the invariant level. -/
theorem invariantPWProjection_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (u : GeoIsotype(ω)) (_hu : u ∈ invLevel(a, ω, Λ)) :
    invariantPWProjection (F := F) (S := S) hs a ω Λ u = u := by
  letI : IsClosed (invLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Definition 11.2.1.3(3), p. 489.
Invariant condensation first projects onto the invariant level, then convolves
and projects onto the weighted theta subspace. -/
def invariantPWCondensation (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ)) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  (onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ)))).comp
    (invariantPWProjection (F := F) (S := S) hs a ω Λ)

/-- Paper: Definition 11.2.1.3(3), p. 489.
On the invariant level, condensation acts by convolution followed by the geometric projection. -/
theorem invariantPWCondensation_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (hφ : supportedAboveOne(φ))
    (u : GeoIsotype(ω)) (_hu : u ∈ invLevel(a, ω, Λ)) :
    invariantPWCondensation (F := F) (S := S) hs a ω Λ φ hφ u =
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by
  have h := invariantPWProjection_apply_of_mem (F := F) (S := S) hs a ω Λ u _hu
  simp only [invariantPWCondensation, ContinuousLinearMap.comp_apply, h]

/-- Projections onto levels squeezed between convergent levels and the target range converge. -/
private theorem invariantPWProjection_tendsto_squeeze
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (A B : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (A i)] [∀ i, CompleteSpace (B i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (A i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))))
    (g : ℝ → ℝ) (hg : Tendsto g atTop atTop) (hAB : ∀ᶠ i in atTop, A (g i) ≤ B i)
    (hBK : ∀ (i : ℝ) (w : I), w ∈ B i → (w : H) ∈ K) (u : I) :
    Tendsto (fun i ↦ (B i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
  have horth (i : ℝ) (w : I) (hw : w ∈ B i) :
      inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H)) - u) w = 0 := by
    have h1 : inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H))) w =
        inner ℂ (u : H) (w : H) := by
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
        Submodule.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr (hBK i w hw)]
    rw [inner_sub_left, h1, Submodule.coe_inner, sub_self]
  have hle (i : ℝ) (hi : A (g i) ≤ B i) :
      ‖(B i).starProjection u - I.orthogonalProjectionOnto (K.starProjection (u : H))‖ ≤
        ‖(A (g i)).starProjection u - I.orthogonalProjectionOnto (K.starProjection (u : H))‖ := by
    have hb : (B i).starProjection u ∈ B i := (B i).starProjection_apply_mem u
    have ha : (A (g i)).starProjection u ∈ B i := hi ((A (g i)).starProjection_apply_mem u)
    have hw : (B i).starProjection u - (A (g i)).starProjection u ∈ B i := (B i).sub_mem hb ha
    have h0 : inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u)
        ((B i).starProjection u - (A (g i)).starProjection u) = 0 := by
      rw [show I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u =
          (I.orthogonalProjectionOnto (K.starProjection (u : H)) - u) + (u - (B i).starProjection u)
          by abel, inner_add_left, horth i _ hw,
        Submodule.starProjection_inner_eq_zero (K := B i) u _ hw, add_zero]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [show I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u +
        ((B i).starProjection u - (A (g i)).starProjection u) =
        I.orthogonalProjectionOnto (K.starProjection (u : H)) - (A (g i)).starProjection u
        by abel] at hp
    rw [norm_sub_rev ((B i).starProjection u), norm_sub_rev ((A (g i)).starProjection u)]
    nlinarith [norm_nonneg (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (A (g i)).starProjection u),
      norm_nonneg (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u),
      norm_nonneg ((B i).starProjection u - (A (g i)).starProjection u)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_iff_norm_sub_tendsto_zero.mp ((hlim u).comp hg))
  filter_upwards [hAB] with i hi using hle i hi

/-- Raising the level to the reciprocal of the place count tends to infinity and stays below it. -/
private theorem invariantPWProjection_tendsto_root (c : ℕ) :
    let g : ℝ → ℝ := fun Λ ↦ Λ ^ (1 / ((c : ℝ) + 1))
    Tendsto g atTop atTop ∧ ∀ᶠ Λ in atTop, 0 < g Λ ∧ g Λ ^ c ≤ Λ := by
  intro g
  let d : ℝ := (c : ℝ) + 1
  have hd : 0 < d := by positivity
  refine ⟨tendsto_rpow_atTop (one_div_pos.mpr hd), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  have hg : 0 < g Λ := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Λ) _
  refine ⟨hg, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  calc Λ ^ (1 / d * c) ≤ Λ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hΛ (by
          rw [div_mul_eq_mul_div, one_mul, div_le_one hd]
          exact le_add_of_nonneg_right zero_le_one)
    _ = Λ := Real.rpow_one Λ

/-- A box of size Λ lies in every product region of size at least Λ to the number of places. -/
private theorem invariantPWProjection_tendsto_abs_le (a : ℝ) (ω : PontryaginDual C₁) {Λ Y : ℝ}
    (hΛ : 0 < Λ) (hY : Λ ^ (Fintype.card (InfinitePlace F) + S.card) ≤ Y) :
    globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ ≤
      globalInvariantPWSobolev (F := F) (S := S) hs a ω Y := by
  have hbox : sLocalPWBox S Λ ⊆ sLocalPWProductRegion S Y := by
    intro x hx
    have ha : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ Λ ^ Fintype.card (InfinitePlace F) := by
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : InfinitePlace F ↦ Λ)
          (fun w _ ↦ pow_nonneg (norm_nonneg (x.1 w)) w.mult) (fun w _ ↦ hx.1 w))
    have hf : (∏ v : S, ‖x.2 v‖) ≤ Λ ^ S.card := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : S ↦ Λ)
          (fun v _ ↦ norm_nonneg (x.2 v)) (fun v _ ↦ hx.2 v))
    change _ * _ ≤ Y
    refine le_trans ?_ hY
    rw [pow_add]
    exact mul_le_mul ha hf (Finset.prod_nonneg fun v _ ↦ norm_nonneg (x.2 v))
      (pow_nonneg hΛ.le _)
  have htests : sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ) ≤
      sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWProductRegion S Y) :=
    Submodule.map_mono (Submodule.span_mono fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩)
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f.val, htests f.property⟩, rfl⟩

/-- The global invariant levels lie in the weighted theta subspace. -/
private theorem invariantPWProjection_tendsto_le_theta (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ ≤
      (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f.val⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo hs ω
  have he := (hj f₀ x rfl).2
  have heq : globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val = (j x).val.val := by
    apply Lp.ext
    exact (withDensity_absolutelyContinuous _ _).ae_le
      ((globalPWThetaSobolevMap_apply (F := F) (S := S) (s := s) a ω f.val).trans he.symm)
  change globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val ∈
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW)
  rw [heq]
  exact (j x).val.property

/-- Paper: Theorem 11.2.1.4(1), p. 489.
The invariant projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem invariantPWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ invariantPWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) := by
  let c : ℕ := Fintype.card (InfinitePlace F) + S.card
  let g : ℝ → ℝ := fun Λ ↦ Λ ^ (1 / ((c : ℝ) + 1))
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let A (Λ : ℝ) : Submodule ℂ I := absLevel(a, ω, Λ)
  let B (Λ : ℝ) : Submodule ℂ I := invLevel(a, ω, Λ)
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (A Λ) := fun Λ ↦
    (show IsClosed (A Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (B Λ) := fun Λ ↦
    (show IsClosed (B Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hpow : ∀ᶠ Λ in atTop, 0 < g Λ ∧ g Λ ^ c ≤ Λ := (invariantPWProjection_tendsto_root c).2
  have hAB : ∀ᶠ Λ in atTop, A (g Λ) ≤ B Λ := by
    filter_upwards [hpow] with Λ hΛ
    exact Submodule.comap_mono
      (invariantPWProjection_tendsto_abs_le (F := F) (S := S) hs a ω hΛ.1 hΛ.2)
  have hBK (Λ : ℝ) (w : I) (hw : w ∈ B Λ) : (w : GeoW) ∈ K :=
    invariantPWProjection_tendsto_le_theta (F := F) (S := S) hs a ω Λ hw
  have hlim (v : I) : Tendsto (fun Λ ↦ (A Λ).starProjection v) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection v))) := by
    with_unfolding_all exact absolutePWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic v
  with_unfolding_all
    exact invariantPWProjection_tendsto_squeeze GeoW I K A B hlim g
      (invariantPWProjection_tendsto_root c).1 hAB hBK u

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
Right multiplication of cutoff geometric convolution by the invariant projections
converges in trace norm.
Deviation: For the fixed cutoff keep the right geometric projection in the
limit. Use the trace class of cutoff convolution on the geometric range. -/
theorem invariantPWCondensation_traceNorm_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ traceNorm
      (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ) -
        T)) atTop (𝓝 0) := by
  intro T
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := (globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ).comap I.subtype
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hlim (u : I) : Tendsto (fun Λ ↦ (levels Λ).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
    with_unfolding_all exact invariantPWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic u
  have hTval : T.val = I.orthogonalProjectionOnto.comp
      (((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))).comp (K.starProjection.comp I.subtypeL)) := by
    with_unfolding_all exact (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose_spec.1
  with_unfolding_all
    exact absolutePWCondensation_traceNorm_tendsto_compressed GeoW I K
      ((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))) levels hlim T hTval

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
The traces of the cutoff invariant condensations converge to the trace of the
cutoff operator composed on the right with the geometric projection.
Deviation: Keep the right geometric projection at the fixed cutoff. -/
theorem invariantPWCondensation_trace_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ hilbertTrace
      (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ))) atTop
      (𝓝 (hilbertTrace T)) := by
  have limit {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : nuclearEndomorphisms H) (A : ℝ → nuclearEndomorphisms H)
      (h : Tendsto (fun r ↦ traceNorm (A r - T)) atTop (𝓝 0)) :
      Tendsto (fun r ↦ hilbertTrace (A r)) atTop (𝓝 (hilbertTrace T)) := by
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub]
    simp only [htr]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _) h
  let T := nuclearRestriction(a, ω, hρ, φ)
  exact limit (H := ↥(GeoIsotype(ω))) T
    (fun r ↦ productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω r))
    (invariantPWCondensation_traceNorm_tendsto (F := F) (S := S) hs a ω _hω _hPic φ _hφ hρ)

end Levels

section Orbital

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "N(" p ", " hs ", " ω ")" => orbitalSobolevSubmodule F (Sₚ(p)) hs ω

variable (F) in
/-- Paper: (11.2.2.1), p. 489. The prime-indexed Sobolev quotient divides the
zero-line isotype by the closed principal-value subspace.
Deviation: Use the closure of the principal-value image from §11.2.0.
Zero-line theta density identifies the completed theta isotype with the ambient one.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev PrimeOrbitalSobolevQuotient (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :=
  ↥(Wω(hs, ω)) ⧸ N(p, hs, ω)

local notation "Q(" p ", " hs ", " ω ")" => PrimeOrbitalSobolevQuotient F p hs ω

/-- Paper: (11.2.2.1), p. 489. In the prime quotient a representative has
zero class exactly when it belongs to the closed principal-value subspace.
Deviation: Use the closed image from §11.2.0. -/
theorem primeOrbitalSobolevQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : Wω(hs, ω)) :
    ((N(p, hs, ω)).mkQ u : Q(p, hs, ω)) = 0 ↔ u ∈ N(p, hs, ω) :=
  Submodule.Quotient.mk_eq_zero _

/-- Paper: (11.2.2.1), p. 489. The prime quotient is separable in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_separable (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    TopologicalSpace.SeparableSpace Q(p, hs, ω) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology W(s) := Lp.SecondCountableTopology
  exact (N(p, hs, ω)).isQuotientMap_mkQL.separableSpace

/-- Paper: (11.2.2.1), p. 489. The prime quotient is complete in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_complete (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    CompleteSpace Q(p, hs, ω) := by
  let : CompleteSpace ↥(Wω(hs, ω)) :=
    (instClosedSpectralIsotypeSec2 (F := F) h₀ hs ω).completeSpace_coe
  exact Submodule.Quotient.completeSpace (N(p, hs, ω))

local notation "P" => adelePolarSubspace F
local notation "testQuot(" χ ")" =>
  (LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P))
local notation "weightedTest(" hs ", " χ ", " f ")" =>
  ((existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
    (globalThetaSobolevInclusion F 0 h₀ hs (Submodule.Quotient.mk (f : P)))).val

/-- A dense map and a dense image of the denominator give the quotient seminorm
by taking the distance to representatives in the test denominator. -/
private theorem primeOrbitalSobolevQuotient_completion_norm
    {X W : Type*} [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (i : X →ₗ[ℂ] W) (D : Submodule ℂ X) (N : Submodule ℂ W)
    (hi : DenseRange i) (hN : (D.map i).topologicalClosure = N) :
    ∃ j : (X ⧸ D) →ₗ[ℂ] W ⧸ N, (∀ x, j (D.mkQ x) = N.mkQ (i x)) ∧
      (∀ x, ‖j (D.mkQ x)‖ = ⨅ v : D, ‖i x - i v.val‖) ∧ DenseRange j := by
  have hle : D.map i ≤ N := hN ▸ Submodule.le_topologicalClosure _
  let j := D.liftQ (N.mkQ.comp i) (fun x hx ↦ (Submodule.Quotient.mk_eq_zero N).2
    (hle (Submodule.mem_map_of_mem hx)))
  refine ⟨j, fun _ ↦ rfl, fun x ↦ ?_, ?_⟩
  · change ‖(Submodule.Quotient.mk (i x) : W ⧸ N)‖ = _
    rw [show ‖(Submodule.Quotient.mk (i x) : W ⧸ N)‖ = Metric.infDist (i x) (N : Set W) from
      QuotientAddGroup.norm_mk _]
    rw [← hN, Submodule.topologicalClosure_coe, Metric.infDist_closure, Metric.infDist_eq_iInf]
    change sInf (range fun y : D.map i ↦ dist (i x) y.val) = _
    apply congrArg sInf
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨v, hv, he⟩ := y.property
      exact ⟨⟨v, hv⟩, by change ‖i x - i v‖ = dist (i x) y.val; rw [he, dist_eq_norm]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨i v.val, Submodule.mem_map_of_mem v.property⟩, dist_eq_norm _ _⟩
  · have hd := N.mkQ_surjective.denseRange.comp hi N.mkQL.continuous
    exact hd.mono (by rintro _ ⟨x, rfl⟩; exact ⟨D.mkQ x, rfl⟩)

/-- A continuous averaging map which is scalar multiplication on its isotype
takes a dense family in an invariant subspace onto a family spanning a dense
subspace of the isotypic intersection. -/
private theorem primeOrbitalSobolevQuotient_completion_projection
    {X W Y : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (I : Y →L[ℂ] W) (π : W →L[ℂ] Y)
    (c : ℂ) (hc : c ≠ 0) (hfix : ∀ y, π (I y) = c • y)
    (A : Submodule ℂ W) (hA : IsClosed (A : Set W)) (z : X → W)
    (hz : closure (range z) = (A : Set W)) (hin : ∀ x, I (π (z x)) ∈ A) :
    (Submodule.span ℂ (range fun x ↦ π (z x))).topologicalClosure = A.comap I.toLinearMap := by
  let D := Submodule.span ℂ (range fun x ↦ π (z x))
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (hA.preimage I.continuous)
    exact Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hin x)
  · intro y hy
    have hm : I y ∈ closure (range z) := hz.symm ▸ hy
    have him : π (I y) ∈ D.topologicalClosure := by
      exact closure_minimal (s := range z) (t := π ⁻¹' (D.topologicalClosure : Set Y))
        (fun _ ⟨x, he⟩ ↦ he ▸ D.le_topologicalClosure (Submodule.subset_span ⟨x, rfl⟩))
        (D.isClosed_topologicalClosure.preimage π.continuous) hm
    have h := D.topologicalClosure.smul_mem c⁻¹ him
    simpa only [hfix, smul_smul, inv_mul_cancel₀ hc, one_smul] using h

/-- Scalar tests of the Pettis average give both its value on an isotype and
its commutation with any operator intertwining the compact group action. -/
private theorem primeOrbitalSobolevQuotient_completion_average
    {G E : Type*} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (μ : Measure G) [IsFiniteMeasure μ]
    (ω : PontryaginDual G) (ρ : G →* (E →L[ℂ] E))
    (A : E →L[ℂ] actionIsotype ρ ω)
    (hA : IsPettisIsotypicAverageOn μ univ ρ ω ((actionIsotype ρ ω).subtypeL.comp A))
    (M : E →L[ℂ] E) (hM : ∀ g x, M (ρ g x) = ρ g (M x)) :
    (∀ y : actionIsotype ρ ω, A y.val = (μ.real univ : ℂ) • y) ∧
      ∀ x, (A (M x)).val = M (A x).val := by
  have hcoeff (x : E) (f : StrongDual ℂ E) :
      f (A x).val = ∫ g, star (ω g : ℂ) * f (ρ g x) ∂μ := by
    obtain ⟨_, hv⟩ := hA x
    have h := LinearMap.congr_fun hv f
    change f (A x).val = ∫ g, f (star (ω g : ℂ) • ρ g x) ∂μ.restrict univ at h
    simpa only [Measure.restrict_univ, map_smul, smul_eq_mul] using h
  constructor
  · intro y
    apply Subtype.ext
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro f
    rw [hcoeff]
    simp [(mem_actionIsotype ..).1 y.property, ← Circle.coe_inv_eq_conj, Complex.real_smul]
  · intro x
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro f
    rw [hcoeff]
    have h := hcoeff x (f.comp M)
    simpa only [ContinuousLinearMap.comp_apply, hM] using h.symm

/-- Projecting a dense family of tests descends to the test quotient. Commutation of
the projection and the principal-value operator identifies the closed denominator. -/
private theorem primeOrbitalSobolevQuotient_completion_assemble
    {G Z W : Type*} [Monoid G] [TopologicalSpace G] [AddCommGroup Z] [Module ℂ Z]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (U : Submodule ℂ W) (hV : ∀ w, w ∈ U)
    (ρ : G →* (U →L[ℂ] U)) (σ : G →* (W →L[ℂ] W)) (ω : PontryaginDual G)
    (hρ : ∀ g (u : U), (ρ g u).val = σ g u.val)
    (A : U →L[ℂ] actionIsotype ρ ω) (M : U →L[ℂ] U)
    (c : ℂ) (hc : c ≠ 0) (hfix : ∀ y : actionIsotype ρ ω, A y.val = c • y)
    (hcomm : ∀ x, (A (M x)).val = M (A x).val)
    (T : Z →ₗ[ℂ] U) (hd : DenseRange T) (K : Submodule ℂ Z) (hk : ∀ z ∈ K, A (T z) = 0)
    (m : Z → Z) (hm : ∀ z, M (T z) = T (m z)) (D : Submodule ℂ (Z ⧸ K))
    (hD : D = Submodule.span ℂ (range fun z ↦ K.mkQ (m z))) (N : Submodule ℂ (actionIsotype σ ω))
    (hNdef : N = ((U.subtype.comp M.toLinearMap).range.topologicalClosure).comap (actionIsotype σ ω).subtype) :
    ∃ (i : (Z ⧸ K) →ₗ[ℂ] actionIsotype σ ω) (j : ((Z ⧸ K) ⧸ D) →ₗ[ℂ] (actionIsotype σ ω ⧸ N)),
      (∀ z, (i (K.mkQ z)).val = (A (T z)).val.val) ∧
      (∀ z, j (D.mkQ (K.mkQ z)) = N.mkQ (i (K.mkQ z))) ∧
      (∀ u, ‖j (D.mkQ u)‖ = ⨅ v : D, ‖i u - i v.val‖) ∧ DenseRange j := by
  let localIso := actionIsotype ρ ω
  let ambientIso := actionIsotype σ ω
  let up : localIso →L[ℂ] ambientIso :=
    (U.subtypeL.comp localIso.subtypeL).codRestrict ambientIso fun u ↦ by
      apply (mem_actionIsotype ..).2
      intro g
      change σ g u.val.val = _
      rw [← hρ g u.val, (mem_actionIsotype ..).1 u.property g]
      rfl
  let down : W →L[ℂ] U := (ContinuousLinearMap.id ℂ W).codRestrict U hV
  let proj := up.comp (A.comp down)
  have hidentity (y : ambientIso) : proj y.val = c • y := by
    let y' : localIso := ⟨down y.val, (mem_actionIsotype ..).2 fun g ↦ Subtype.ext (by
      change (ρ g (down y.val)).val = (ω g : ℂ) • y.val
      rw [hρ]; exact (mem_actionIsotype ..).1 y.property g)⟩
    change up (A y'.val) = c • y
    rw [hfix, map_smul]
    rfl
  let i := K.liftQ (up.toLinearMap.comp (A.toLinearMap.comp T)) fun z hz ↦ by
    change up (A (T z)) = 0
    rw [hk z hz, map_zero]
  have hsurj : Surjective (up.comp A) := by
    intro y
    refine ⟨c⁻¹ • down y.val, ?_⟩
    rw [map_smul]
    change c⁻¹ • proj y.val = y
    rw [hidentity, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hi : DenseRange i := (hsurj.denseRange.comp hd (up.comp A).continuous).mono
    (by rintro _ ⟨z, rfl⟩; exact ⟨K.mkQ z, rfl⟩)
  let R := (U.subtype.comp M.toLinearMap).range
  let f := U.subtypeL.comp M
  let z := fun z ↦ f (T z)
  have hz : closure (range z) = (R.topologicalClosure : Set W) := by
    change closure (range (f ∘ T)) = closure (range f)
    rw [Set.range_comp]
    exact le_antisymm (closure_mono (image_subset_range _ _))
      (closure_minimal (f.continuous.range_subset_closure_image_dense hd) isClosed_closure)
  have hN : (D.map i).topologicalClosure = N := by
    have hspan : D.map i = Submodule.span ℂ (range fun x ↦ proj (z x)) := by
      rw [hD, Submodule.map_span, ← Set.range_comp]
      apply congrArg (Submodule.span ℂ)
      apply congrArg range
      funext x
      change up (A (T (m x))) = up (A (M (T x)))
      rw [hm]
    rw [hspan, hNdef]
    apply primeOrbitalSobolevQuotient_completion_projection ambientIso.subtypeL proj c hc hidentity
      R.topologicalClosure R.isClosed_topologicalClosure z hz
    intro x
    apply R.le_topologicalClosure
    exact ⟨(A (T x)).val, (congrArg Subtype.val (hcomm (T x))).symm⟩
  obtain ⟨j, hj, hjnorm, hjdense⟩ := primeOrbitalSobolevQuotient_completion_norm i D N hi hN
  exact ⟨i, j, fun _ ↦ rfl, fun z ↦ hj (K.mkQ z), hjnorm, hjdense⟩

/-- On a test in the restricted homogeneous theta kernel the weighted average vanishes,
since its homogeneous class is the zero polar-free class. -/
private theorem primeOrbitalSobolevQuotient_completion_kernel (χ : PontryaginDual C𝔽)
    {s : ℝ} (hs : 0 ≤ s) (f : P) (hf : f ∈ testQuot(χ)) :
    (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
      (globalThetaSobolevInclusion F 0 h₀ hs (Submodule.Quotient.mk f)) = 0 := by
  let h := exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) h₀ hs (ω(χ))
  have he : (Submodule.Quotient.mk f.val : _ ⧸ (homogeneousAdelicThetaLinearMap F (ω(χ))).ker) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hf
  have hv := (h.choose_spec.2.2 f 0 he.symm).1
  exact hv.symm.trans h.choose.map_zero


/-- Paper: Paragraph after (11.2.2.1), p. 490.
The §7.4 test quotient maps densely into the Sobolev quotient. Its pulled-back norm
is the quotient seminorm of the weighted tests modulo the test principal-value image.
Deviation: Take the separated completion for the potentially degenerate seminorm. -/
theorem primeOrbitalSobolevQuotient_completion (χ : PontryaginDual C𝔽)
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s) :
    ∃ (i : (P ⧸ testQuot(χ)) →ₗ[ℂ] Wω(hs, ω(χ)))
      (j : FiniteNuclearityQuotient χ p →ₗ[ℂ] Q(p, hs, ω(χ))),
      (∀ f : P, ((i ((testQuot(χ)).mkQ f)) : W(s)) = weightedTest(hs, χ, f)) ∧
      (∀ f : P,
        j ((finiteNuclearityDenominator χ p).mkQ ((testQuot(χ)).mkQ f)) =
          (N(p, hs, ω(χ))).mkQ (i ((testQuot(χ)).mkQ f))) ∧
      (∀ u : P ⧸ testQuot(χ),
        ‖j ((finiteNuclearityDenominator χ p).mkQ u)‖ =
          ⨅ v : finiteNuclearityDenominator χ p, ‖i u - i v.val‖) ∧ DenseRange j := by
  let U := globalThetaSobolev F 0 h₀ hs
  let J := globalThetaSobolevInclusion F 0 h₀ hs
  let K₀ := (LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype
  let T := J.toLinearMap.comp K₀.mkQ
  let R := (exists_globalThetaSobolevAction (F := F) 0 h₀ hs).choose
  let ρ := R.comp (ideleClassNorm F).ker.subtype
  let σ := (hardySobolevTranslation μ𝔽 m𝔽 0 0 s h₀ hs).comp (ideleClassNorm F).ker.subtype
  let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
  let M := globalThetaSobolevPrincipalValue F (Sₚ(p)) 0 hs
  let m (f : P) : P := ⟨adelePrincipalValue F (Sₚ(p)) f.val, nuclearityPrincipalValue_mem_polar p f⟩
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hmass : (μ₁.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos.ne')
  have hA : IsPettisIsotypicAverageOn μ₁ univ ρ (ω(χ)) ((actionIsotype ρ (ω(χ))).subtypeL.comp A) :=
    (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose_spec.1
  have hM (g : C₁) (y : U) : M (ρ g y) = ρ g (M y) :=
    globalThetaSobolevPrincipalValue_equivariant (Sₚ(p)) 0 hs g y
  have hraw := primeOrbitalSobolevQuotient_completion_average (G := C₁) (E := ↥U) μ₁ (ω(χ)) ρ A hA M hM
  have hU (w : W(s)) : w ∈ U := by
    exact closure_minimal (s := range fun x : GlobalPolarFreeThetaSpace F ↦ (J x).val)
      (t := (U : Set W(s))) (by rintro _ ⟨x, rfl⟩; exact (J x).property)
      (globalThetaSobolev_closed_complete_separable (F := F) 0 h₀ hs).1
      (denseRange_globalTheta_zeroLine (F := F) hs w)
  have hρ (g : C₁) (y : U) : (ρ g y).val = σ g y.val :=
    (exists_globalThetaSobolevAction (F := F) 0 h₀ hs).choose_spec.1 g.val y
  have hd : DenseRange T := (globalThetaSobolev_dense (F := F) 0 h₀ hs).comp
    K₀.mkQ_surjective.denseRange J.continuous
  have hm (f : P) : M (T f) = T (m f) :=
    globalThetaSobolevPrincipalValue_apply (Sₚ(p)) 0 hs f
  have hk (f : P) (hf : f ∈ testQuot(χ)) : A (T f) = 0 := by
    dsimp only [A, T, J, K₀, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.mkQ_apply]
    exact primeOrbitalSobolevQuotient_completion_kernel χ hs f hf
  have hD : finiteNuclearityDenominator χ p =
      Submodule.span ℂ (range fun z : P ↦ (testQuot(χ)).mkQ (m z)) := by
    unfold finiteNuclearityDenominator
    simp only [m, Submodule.mkQ_apply]
  have hN : N(p, hs, ω(χ)) =
      ((U.subtype.comp M.toLinearMap).range.topologicalClosure).comap (actionIsotype σ (ω(χ))).subtype := by
    unfold orbitalSobolevSubmodule
    dsimp only [U, M, σ]
  have hresult := primeOrbitalSobolevQuotient_completion_assemble (G := C₁) (Z := ↥P) (W := W(s))
    U hU ρ σ (ω(χ)) hρ A M _ hmass hraw.1 hraw.2 T hd (testQuot(χ)) hk m hm
    (finiteNuclearityDenominator χ p) hD (N(p, hs, ω(χ))) hN
  obtain ⟨i, j, hi, hj, hnorm, hjdense⟩ := hresult
  let toTestQuotient : FiniteNuclearityQuotient χ p →ₗ[ℂ]
      ((P ⧸ testQuot(χ)) ⧸ finiteNuclearityDenominator χ p) :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨i, j.comp toTestQuotient, ?_, ?_, ?_, ?_⟩
  · exact hi
  · exact hj
  · exact hnorm
  · exact hjdense

variable (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
  (ω : PontryaginDual (ideleClassNorm F).ker)

local notation "Aω(" φ ")" => ContinuousLinearMap.restrict (A(hs, φ))
  (hardySobolevTestAction_preserves_spectralIsotype (F := F) h₀ hs ω φ)

/-- Paper: (11.2.2.1)–(11.2.2.3), pp. 489–490.
Convolution preserves the closed principal-value subspace of the zero-line isotype.
Deviation: Use the closure of the principal-value image. -/
theorem primeOrbitalSobolevSubmodule_convolution_invariant (φ : BruhatCompactSupport C𝔽) :
    N(p, hs, ω) ≤ ((N(p, hs, ω)).mkQL.comp (Aω(φ))).ker := by sorry

/-- An operator whose composite with the quotient map kills the denominator descends uniquely. -/
private theorem existsUnique_primeOrbitalSobolevConvolution_lift
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (N : Submodule ℂ E) (A : E →L[ℂ] E)
    (hN : N ≤ (N.mkQL.comp A).ker) :
    ∃! C : (E ⧸ N) →L[ℂ] (E ⧸ N),
      ∀ u : E, C (N.mkQ u) = N.mkQ (A u) := by
  let C : (E ⧸ N) →L[ℂ] (E ⧸ N) := N.liftQL (N.mkQL.comp A) hN
  refine ⟨C, fun u ↦ rfl, ?_⟩
  intro D hD
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨u, rfl⟩ := N.mkQ_surjective q
  exact hD u

/-- Paper: (11.2.2.3), p. 490.
The action on representatives determines a unique continuous linear map on the prime quotient.
Deviation: Use the closed principal-value denominator. -/
theorem existsUnique_primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :
    ∃! C : Q(p, hs, ω) →L[ℂ] Q(p, hs, ω), ∀ u : Wω(hs, ω),
      C ((N(p, hs, ω)).mkQ u) = (N(p, hs, ω)).mkQ (Aω(φ) u) := by
  exact existsUnique_primeOrbitalSobolevConvolution_lift
    (N(p, hs, ω)) (Aω(φ))
    (primeOrbitalSobolevSubmodule_convolution_invariant (F := F) p hs ω φ)

/-- Paper: (11.2.2.3), p. 490.
The prime orbital action is the convolution operator descended to the zero-line quotient.
Deviation: Use the closed principal-value denominator. -/
def primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :=
  (existsUnique_primeOrbitalSobolevConvolution (F := F) p hs ω φ).exists.choose

/-- Paper: (11.2.2.3), p. 490.
The orbital convolution of a quotient class is the class of the representative's convolution. -/
theorem primeOrbitalSobolevConvolution_mkQ (φ : BruhatCompactSupport C𝔽) (u : Wω(hs, ω)) :
    primeOrbitalSobolevConvolution (F := F) p hs ω φ ((N(p, hs, ω)).mkQ u) =
      (N(p, hs, ω)).mkQ (Aω(φ) u) := by
  exact (existsUnique_primeOrbitalSobolevConvolution (F := F) p hs ω φ).exists.choose_spec u

-- TODO(paper-gap): Corollary 11.2.0.5 bounds the jets but gives no upper
-- bound on their biorthogonals. The single-prime trace proof needs its own
-- estimate. For the §11.2.0 basis at one prime, multiplication by
-- |g|^(2πi / log p) shifts the jets unitarily and permutes their
-- biorthogonals. There are only finitely many orbits, including jet order.
-- In (11.2.2.12) the displayed summands act on the primal quotient. For
-- the transpose the input is a functional ℓ and each term is ℓ(ψⱼ) A'ηⱼ.
-- Page 496 invokes this expansion on PW levels and needs a common level
-- for its chosen representatives as well as the kernel comparison.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
variable (h₁ : 1 < s) (_hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
variable (_hχ : ∀ v ∈ (finite_nuclearityPlacesAbove (F := F) p).toFinset,
  (ideleClassNormTwist χ 0).IsUnramifiedAt v)

include _hdeg _hχ

local notation "hs₁" => (zero_lt_one.trans h₁).le
local notation "OrbQ" => Q(p, hs₁, ω(χ))
local notation "OrbA(" φ ")" => primeOrbitalSobolevConvolution (F := F) p hs₁ (ω(χ)) φ

local notation "onClosedPrimeQuotient(" hs ", " ω ", " body ")" =>
  (let hN := instClosedOrbitalSobolevSubmoduleSec2a (F := F) (Sₚ(p)) hs ω
   letI : IsClosed (N(p, hs, ω) : Set Wω(hs, ω)) := hN
   letI : CompleteSpace ↥(Wω(hs, ω)) :=
     (instClosedSpectralIsotypeSec2 (F := F) h₀ hs ω).completeSpace_coe
   letI : CompleteSpace ↥(N(p, hs, ω)) := hN.completeSpace_coe
   letI : NormedAddCommGroup Q(p, hs, ω) := Submodule.Quotient.normedAddCommGroup (N(p, hs, ω))
   letI : InnerProductSpace ℂ Q(p, hs, ω) := Submodule.instQuotientInnerProductSpace (N(p, hs, ω))
   letI : CompleteSpace Q(p, hs, ω) := Submodule.Quotient.completeSpace (N(p, hs, ω))
   body)

/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490.
The convolution action lifts linearly to the trace class and is continuous in trace norm.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_traceNorm_continuous :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∃ L : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms OrbQ,
        (∀ φ, (L φ).val = OrbA(φ)) ∧ Tendsto (fun φ ↦ traceNorm (L φ)) (𝓝 0) (𝓝 0)) :=
  by sorry

section PrimeOrbitalNuclearHelpers

omit _hdeg _hχ

/-- Polynormable structures with the same topology have only proof fields. -/
private theorem primeOrbitalSobolevConvolution_nuclear_polynormable_independent
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p₁ p₂ : PolynormableSpace ℂ H) (A : H →L[ℂ] H) :
    @IsNuclearOperator H H _ _ _ p₁ _ _ _ A ↔ @IsNuclearOperator H H _ _ _ p₂ _ _ _ A := by
  have hp : p₁ = p₂ := by cases p₁; cases p₂; rfl
  cases hp
  rfl

/-- Extract nuclearity before specializing to the quotient instance tower. -/
private theorem primeOrbitalSobolevConvolution_nuclear_of_lift
    (H X : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (A : X → H →L[ℂ] H)
    (h : ∃ L : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (L x).val = A x) ∧
      Tendsto (fun x ↦ traceNorm (L x)) (𝓝 0) (𝓝 0)) (x : X) :
    letI : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
    IsNuclearOperator (A x) := by
  obtain ⟨L, hL, _⟩ := h
  have hn := (L x).property
  rw [hL x] at hn
  exact (primeOrbitalSobolevConvolution_nuclear_polynormable_independent H
    (inferInstance : PolynormableSpace ℂ H)
    ((norm_withSeminorms ℂ H).toPolynormableSpace) (A x)).mp hn

end PrimeOrbitalNuclearHelpers

/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490.
Convolution by any compactly supported Bruhat test on the prime quotient is trace class.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_nuclear (φ : BruhatCompactSupport C𝔽) :
    onClosedPrimeQuotient(hs₁, ω(χ),
      letI : PolynormableSpace ℂ OrbQ := (norm_withSeminorms ℂ OrbQ).toPolynormableSpace
      IsNuclearOperator (OrbA(φ))) := by
  have hn := primeOrbitalSobolevConvolution_traceNorm_continuous (F := F) (p := p)
    (χ := χ) (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ)
  exact onClosedPrimeQuotient(hs₁, ω(χ), by
    apply primeOrbitalSobolevConvolution_nuclear_of_lift OrbQ (BruhatCompactSupport C𝔽)
      (fun ψ ↦ OrbA(ψ)) hn φ)

/-- Paper: Theorem 11.2.2.1, p. 490.
Taking the trace of prime orbital convolution gives a distribution on the compactly
supported Bruhat test space.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_trace_distribution :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
        ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms OrbQ),
          T.val = OrbA(φ) → D φ = hilbertTrace T) := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  have hn := primeOrbitalSobolevConvolution_traceNorm_continuous (F := F) (p := p)
    (χ := χ) (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ)
  exact onClosedPrimeQuotient(hs₁, ω(χ), by
    apply traceDistribution (X := BruhatCompactSupport C𝔽) (H := OrbQ) (fun φ ↦ OrbA(φ))
    exact hn)

local notation "zeros" => {z : ℂ // reciprocalPartialHeckeEulerProduct χ (Sₚ(p)) z = 0}
local notation "mult(" z ")" => orbitalEulerMultiplicity χ (Sₚ(p)) z

/-- Paper: Theorem 11.2.2.1 and (11.2.2.4)–(11.2.2.5), p. 490. The Mellin values of the
test at the zeros of the reciprocal partial Euler product over the places above p, weighted
by the admissible multiplicity, form an absolutely summable family. -/
theorem primeOrbitalSobolevConvolution_trace_summable (φ : BruhatCompactSupport C𝔽) :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
        let term (z : zeros) :=
          (spectralBoundaryMultiplicity s (mult(z.val)) : ℂ) * nuclearityTestMellin χ φ z.val
        Summable (fun z ↦ ‖term z‖)) := by sorry

/-- Paper: Theorem 11.2.2.1 and (11.2.2.4)–(11.2.2.5), p. 490. The sum of those weighted
Mellin values is the trace of the convolution, for any nuclear presentation of it. -/
theorem primeOrbitalSobolevConvolution_trace_hasSum (φ : BruhatCompactSupport C𝔽) :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
        let term (z : zeros) :=
          (spectralBoundaryMultiplicity s (mult(z.val)) : ℂ) * nuclearityTestMellin χ φ z.val
        HasSum term (hilbertTrace T)) := by sorry

/-- Paper: Theorem 11.2.2.1 and (11.2.2.4)–(11.2.2.5), p. 490.
The trace is the absolutely convergent sum of Mellin values at the zeros of the
reciprocal Euler product over the places above p, weighted by admissible multiplicity.
Deviation: Use the closed denominator and the strict boundary cutoff of §11.2.0.
Under the stated degree bound this cutoff agrees with the printed one. -/
theorem primeOrbitalSobolevConvolution_trace (φ : BruhatCompactSupport C𝔽) :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
        let term (z : zeros) :=
          (spectralBoundaryMultiplicity s (mult(z.val)) : ℂ) * nuclearityTestMellin χ φ z.val
        Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace T)) :=
  fun T hT => And.intro
    (primeOrbitalSobolevConvolution_trace_summable (F := F) (p := p) (s := s) (χ := χ)
      (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ) φ T hT)
    (primeOrbitalSobolevConvolution_trace_hasSum (F := F) (p := p) (s := s) (χ := χ)
      (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ) φ T hT)

include h₁ in
/-- Paper: Remark 11.2.2.2, p. 491.
The degree bound admits all jet orders below the multiplicity of a prime Euler zero.
The strict integrability cutoff then leaves that multiplicity unchanged. -/
theorem primeOrbitalMultiplicity_saturates (z : zeros) :
    spectralBoundaryMultiplicity s (mult(z.val)) = mult(z.val) := by
  classical
  let S := Sₚ(p)
  have hcard : S.card ≤ Module.finrank ℚ F := by
    let e (v : S) : p.asIdeal.primesOver (𝓞 F) :=
      ⟨v.val.asIdeal, v.val.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal
        (show v.val.under (𝓞 ℚ) = p from (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp v.property)).symm⟩⟩
    have hi : Function.Injective e := fun v w h ↦
      Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
    simpa only [Fintype.card_coe] using (Fintype.card_le_of_injective e hi).trans
      (reciprocalEulerProduct_over_prime_order_le_card_le (F := F) p)
  have hm : mult(z.val) ≤ Module.finrank ℚ F := by
    rw [orbitalEulerMultiplicity_eq_card]
    exact (Finset.card_filter_le _ _).trans hcard
  apply Nat.le_antisymm (min_le_left _ _)
  by_contra! hlt
  have hk : (spectralBoundaryMultiplicity s (mult(z.val)) : ℝ) + 1 ≤ Module.finrank ℚ F := by
    exact_mod_cast (Nat.succ_le_of_lt hlt).trans hm
  have himp := (lt_spectralBoundaryMultiplicity s (mult(z.val))
    (spectralBoundaryMultiplicity s (mult(z.val)))).mpr ⟨hlt, by linarith only [hk, _hdeg]⟩
  exact (lt_irrefl _ himp)

/-- Paper: Remark 11.2.2.2 and (11.2.2.13), p. 491.
The prime orbital convolution trace is independent of the Sobolev degree
once both degrees satisfy the two lower bounds.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_trace_eq_of_degree {s' : ℝ} (h₁' : 1 < s')
    (_hdeg' : 2 * (Module.finrank ℚ F : ℝ) ≤ s') (φ : BruhatCompactSupport C𝔽) :
    let hs' := (zero_lt_one.trans h₁').le
    onClosedPrimeQuotient(hs₁, ω(χ),
      onClosedPrimeQuotient(hs', ω(χ),
        ∀ (T : nuclearEndomorphisms OrbQ) (T' : nuclearEndomorphisms Q(p, hs', ω(χ))),
          T.val = OrbA(φ) →
          T'.val = primeOrbitalSobolevConvolution (F := F) p hs' (ω(χ)) φ →
          hilbertTrace T = hilbertTrace T')) := by
  dsimp only
  intro T T' hT hT'
  have hsum := (primeOrbitalSobolevConvolution_trace (F := F) p χ h₁ _hdeg _hχ φ T hT).2
  have hsum' := (primeOrbitalSobolevConvolution_trace (F := F) p χ h₁' _hdeg' _hχ φ T' hT').2
  apply hsum.unique
  apply hsum'.congr_fun
  intro z
  rw [primeOrbitalMultiplicity_saturates (F := F) p χ h₁ _hdeg _hχ z,
    primeOrbitalMultiplicity_saturates (F := F) p χ h₁' _hdeg' _hχ z]

end Orbital

end RiemannMasullo
