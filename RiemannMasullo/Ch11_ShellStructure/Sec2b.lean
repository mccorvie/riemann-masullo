module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2b

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
    MemLp (localWeightedTheta(a, ω, f)) 2 localWMeasure := by sorry

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Send a local polar-free test to its weighted homogeneous theta class.
Deviation: Use the positive local twist of the Sobolev embedding. -/
def sLocalPWThetaSobolevMap {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁)
    (f : Zₛ) :=
  MemLp.toLp (localWeightedTheta(a, ω, f))
    (sLocalPWTheta_memLp (F := F) (S := S) (s := s) ha ω f)

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
The local Sobolev map is represented almost everywhere by the weighted homogeneous theta. -/
theorem sLocalPWThetaSobolevMap_apply {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (f : Zₛ) :
    (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f : SIdeleQuotient F S → ℂ) =ᵐ[sLocalQuotientTamagawaMeasure F S]
      localWeightedTheta(a, ω, f) := by sorry

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
Globalized polar-free tests yield weighted Sobolev vectors.
Deviation: Use direct integer-indicator insertion as in the repaired §7.3.2. -/
theorem globalPWTheta_memLp (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    MemLp (globalWeightedTheta(a, ω, f)) 2 globalWMeasure := by sorry

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
      globalWeightedTheta(a, ω, f) := by sorry

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
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalAbsolutePWSobolev (F := F) (S := S) hs ha ω Λ := by sorry

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
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ := by sorry

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
    absolutePWProjection (F := F) (S := S) hs a ω Λ u = u := by sorry

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
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by sorry

local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "Pgeom(" a ", " ω ")" => onIsotype(ω, ambientGeom(a))

/-- Paper: Theorem 11.2.1.2(1), p. 488.
The absolute projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem absolutePWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ absolutePWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) :=
  by sorry

variable {R ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

local notation "cutoffConv(" a ", " ω ", " hρ ", " φ ")" =>
  onIsotype(ω, geometricTruncatedConvolution (F := F) a h₀ hs hρ φ)
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

-- At a fixed cutoff the uncompressed operator may have a different trace.
-- On theta inputs Q A Q = A Q, so cutoff condensation only needs the
-- trace class of Mρ A Q. Cutoff convolution Mρ A is already trace class
-- by §9.3.3 (a larger smooth cutoff can be chosen to cover tsupport ρ).

/-- Paper: Theorems 11.2.1.2(2) and 11.2.1.4(2), pp. 488–489.
The cutoff geometric restriction is trace class on the chosen isotype.
It agrees with cutoff geometric convolution after any map into theta.
Deviation: Use the right-compressed operator for the corrected limits. -/
theorem exists_nuclear_geometricPWRestriction (a : ℝ) (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    ∃ T : nuclearEndomorphisms GeoIsotype(ω),
      T.val = onIsotype(ω, geometricRestriction (F := F) a h₀ hs hρ φ) ∧
      ∀ P : GeoIsotype(ω) →L[ℂ] GeoIsotype(ω), Pgeom(a, ω) * P = P →
        T.val * P = cutoffConv(a, ω, hρ, φ) * P := by sorry

local notation "nuclearRestriction(" a ", " ω ", " hρ ", " φ ")" =>
  (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose

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
        T)) atTop (𝓝 0) := by sorry

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
      (𝓝 (hilbertTrace T)) := by sorry

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
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ := by sorry

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
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ := by sorry

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
    invariantPWProjection (F := F) (S := S) hs a ω Λ u = u := by sorry

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
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by sorry

/-- Paper: Theorem 11.2.1.4(1), p. 489.
The invariant projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem invariantPWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ invariantPWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) :=
  by sorry

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
        T)) atTop (𝓝 0) := by sorry

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
      (𝓝 (hilbertTrace T)) := by sorry

end Levels

section Orbital

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "N(" p ", " hs ", " ω ")" => orbitalSobolevSubmodule F (Sₚ(p)) hs ω

variable (F) in
/-- Paper: (11.2.2.1), p. 489. The prime-indexed Sobolev quotient divides the
zero-line isotype by the closed principal-value subspace.
Deviation: Use the closure of the principal-value image from §11.2.0.
Zero-line theta density identifies the completed theta isotype with the ambient one. -/
abbrev PrimeOrbitalSobolevQuotient (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :=
  ↥(Wω(hs, ω)) ⧸ N(p, hs, ω)

local notation "Q(" p ", " hs ", " ω ")" => PrimeOrbitalSobolevQuotient F p hs ω

/-- Paper: (11.2.2.1), p. 489. In the prime quotient a representative has
zero class exactly when it belongs to the closed principal-value subspace.
Deviation: Use the closed image from §11.2.0. -/
theorem primeOrbitalSobolevQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : Wω(hs, ω)) :
    ((N(p, hs, ω)).mkQ u : Q(p, hs, ω)) = 0 ↔ u ∈ N(p, hs, ω) := by sorry

/-- Paper: (11.2.2.1), p. 489. The prime quotient is separable in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_separable (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    TopologicalSpace.SeparableSpace Q(p, hs, ω) := by sorry

/-- Paper: (11.2.2.1), p. 489. The prime quotient is complete in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_complete (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    CompleteSpace Q(p, hs, ω) := by sorry

local notation "P" => adelePolarSubspace F
local notation "testQuot(" χ ")" =>
  (LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P))
local notation "weightedTest(" hs ", " χ ", " f ")" =>
  ((existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
    (globalThetaSobolevInclusion F 0 h₀ hs (Submodule.Quotient.mk (f : P)))).val

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
          ⨅ v : finiteNuclearityDenominator χ p, ‖i u - i v.val‖) ∧ DenseRange j := by sorry

variable (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
  (ω : PontryaginDual (ideleClassNorm F).ker)

local notation "Aω(" φ ")" => ContinuousLinearMap.restrict (A(hs, φ))
  (hardySobolevTestAction_preserves_spectralIsotype (F := F) h₀ hs ω φ)

/-- Paper: (11.2.2.1)–(11.2.2.3), pp. 489–490.
Convolution preserves the closed principal-value subspace of the zero-line isotype.
Deviation: Use the closure of the principal-value image. -/
theorem primeOrbitalSobolevSubmodule_convolution_invariant (φ : BruhatCompactSupport C𝔽) :
    N(p, hs, ω) ≤ ((N(p, hs, ω)).mkQL.comp (Aω(φ))).ker := by sorry

/-- Paper: (11.2.2.3), p. 490.
The action on representatives determines a unique continuous linear map on the prime quotient.
Deviation: Use the closed principal-value denominator. -/
theorem existsUnique_primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :
    ∃! C : Q(p, hs, ω) →L[ℂ] Q(p, hs, ω), ∀ u : Wω(hs, ω),
      C ((N(p, hs, ω)).mkQ u) = (N(p, hs, ω)).mkQ (Aω(φ) u) := by sorry

/-- Paper: (11.2.2.3), p. 490.
The prime orbital action is the convolution operator descended to the zero-line quotient.
Deviation: Use the closed principal-value denominator. -/
def primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :=
  (existsUnique_primeOrbitalSobolevConvolution (F := F) p hs ω φ).exists.choose

/-- Paper: (11.2.2.3), p. 490.
The orbital convolution of a quotient class is the class of the representative's convolution. -/
theorem primeOrbitalSobolevConvolution_mkQ (φ : BruhatCompactSupport C𝔽) (u : Wω(hs, ω)) :
    primeOrbitalSobolevConvolution (F := F) p hs ω φ ((N(p, hs, ω)).mkQ u) =
      (N(p, hs, ω)).mkQ (Aω(φ) u) := by sorry

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
Convolution by any compactly supported Bruhat test on the prime quotient is trace class.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_nuclear (φ : BruhatCompactSupport C𝔽) :
    onClosedPrimeQuotient(hs₁, ω(χ),
      letI : PolynormableSpace ℂ OrbQ := (norm_withSeminorms ℂ OrbQ).toPolynormableSpace
      IsNuclearOperator (OrbA(φ))) := by sorry

/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490.
The convolution action lifts linearly to the trace class and is continuous in trace norm.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_traceNorm_continuous :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∃ L : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms OrbQ,
        (∀ φ, (L φ).val = OrbA(φ)) ∧ Tendsto (fun φ ↦ traceNorm (L φ)) (𝓝 0) (𝓝 0)) :=
  by sorry

/-- Paper: Theorem 11.2.2.1, p. 490.
Taking the trace of prime orbital convolution gives a distribution on the compactly
supported Bruhat test space.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_trace_distribution :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
        ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms OrbQ),
          T.val = OrbA(φ) → D φ = hilbertTrace T) := by sorry

local notation "zeros" => {z : ℂ // reciprocalPartialHeckeEulerProduct χ (Sₚ(p)) z = 0}
local notation "mult(" z ")" => orbitalEulerMultiplicity χ (Sₚ(p)) z

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
        Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace T)) := by sorry

include h₁ in
/-- Paper: Remark 11.2.2.2, p. 491.
The degree bound admits all jet orders below the multiplicity of a prime Euler zero.
The strict integrability cutoff then leaves that multiplicity unchanged. -/
theorem primeOrbitalMultiplicity_saturates (z : zeros) :
    spectralBoundaryMultiplicity s (mult(z.val)) = mult(z.val) := by sorry

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
          hilbertTrace T = hilbertTrace T')) := by sorry

end Orbital

end RiemannMasullo
