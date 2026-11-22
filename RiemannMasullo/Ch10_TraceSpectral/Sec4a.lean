module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Analysis.Normed.Module.DoubleDual
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.AppC_LCTVS.Sec3a
import all RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Spectral and geometric truncations

Masullo, §§10.4.1–10.4.2, pp. 455–464. The operators act on the compact-interval
Hardy–Sobolev space. Its spectral quotient is represented by the orthogonal
complement of the closed weighted theta subspace.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

section Truncations

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "Θ(" a ", " hα ", " hs ")" => globalThetaSobolev F a (hStrip(hα)) hs
local notation "H(" a ", " hα ", " hs ")" => spectralSobolevQuotient F a (hStrip(hα)) hs

variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "W₀" => W(α, s)
local notation "Θ₀" => Θ(a, hα, hs)
local notation "H₀" => H(a, hα, hs)
local notation "Qₐ" => (Θ₀).mkQL
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ
local notation "Aₛ(" φ ")" => spectralConvolution (F := F) a (hStrip(hα)) hs φ
local notation "M(" hρ ")" => modulatedCutoffOperator m𝔽
  ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm g))) hρ

-- Use the same norm-generated locally convex structure as in §10.3.
attribute [local instance] instSpectralQuotientPolynormableSec3

local notation "quotientNuclear(" φ ")" => IsNuclearOperator (E := H₀) (F := H₀) (Aₛ(φ))

-- On p. 455 the introduction calls the range of a smooth cutoff multiplier closed.
-- A profile tending continuously to zero at the edge of its support need not
-- have closed multiplier range. Taking its closure is an additional operation.

/-- Paper: Definition 10.4.1.1(1), p. 456. The geometric projection is the
orthogonal projector onto the closed weighted theta subspace.
Deviation: The projector exists for every real twist, as used in Definition 10.4.1.3. -/
def geometricProjection : W₀ →L[ℂ] W₀ :=
  (Θ₀).starProjection

/-- Paper: Definition 10.4.1.1(2), p. 456. The spectral projection is the
orthogonal projector onto the complement of the closed weighted theta subspace.
Deviation: The projector exists for every real twist, as used in Definition 10.4.1.3. -/
def spectralProjection : W₀ →L[ℂ] W₀ :=
  (Θ₀).orthogonal.starProjection

local notation "Pgeom" => geometricProjection (F := F) a hα hs
local notation "Pspec" => spectralProjection (F := F) a hα hs

/-- Helper for `geometricTruncation_apply_of_mem` and `spectralTruncation_apply_of_mem`. -/
private theorem w18_comp_apply_of_fix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P : E →L[ℂ] E) (u : E) (h : P u = u) : (T.comp P) u = T u := by
  simp [h]

/-- Helper for the truncated convolutions. -/
private theorem w18_comp_comp_apply_of_fix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P A : E →L[ℂ] E) (u : E) (h : P (A u) = A u) : ((T.comp P).comp A) u = T (A u) := by
  simp [h]

/-- Helper for the restrictions. -/
private theorem w18_comp_comp_apply_of_fix' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P A : E →L[ℂ] E) (u : E) (h : P u = u) : (T.comp (A.comp P)) u = T (A u) := by
  simp [h]

/-- Helper for `geometricTruncation_add_spectralTruncation`. -/
private theorem w18_comp_add_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P Q : E →L[ℂ] E) (h : ∀ u, P u + Q u = u) : T.comp P + T.comp Q = T := by
  ext u
  simp [← map_add, h]

/-- Paper: Definition 10.4.1.1(1), p. 456. The geometric projector fixes each
vector in the theta subspace. -/
theorem geometricProjection_apply_of_mem {u : W₀} (_hu : u ∈ Θ₀) :
    Pgeom u = u :=
  (Θ₀).starProjection_eq_self_iff.2 _hu

/-- Paper: Definition 10.4.1.1(2), p. 456. The spectral projector fixes each
vector orthogonal to the theta subspace. -/
theorem spectralProjection_apply_of_mem {u : W₀} (_hu : u ∈ (Θ₀).orthogonal) :
    Pspec u = u := by
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Lemma 10.4.1.2, p. 456. The spectral projection preserves the
quotient class of every vector. -/
theorem spectralQuotient_comp_spectralProjection (_ha : 0 < a) :
    (Qₐ).comp Pspec = Qₐ :=
  ContinuousLinearMap.ext fun u ↦ ((Submodule.Quotient.eq (Θ₀)).2 (by
    have h : u - Pspec u = (Θ₀).starProjection u :=
      sub_eq_of_eq_add ((Θ₀).starProjection_add_starProjection_orthogonal u).symm
    exact (congrArg (· ∈ Θ₀) h).mpr ((Θ₀).starProjection_apply_mem u))).symm

/-- Paper: Lemma 10.4.1.2, p. 456. The geometric projection has zero
composition with the quotient map. -/
theorem spectralQuotient_comp_geometricProjection (_ha : 0 < a) :
    (Qₐ).comp Pgeom = 0 :=
  ContinuousLinearMap.ext fun u ↦
    (Submodule.Quotient.mk_eq_zero (Θ₀)).2 ((Θ₀).starProjection_apply_mem u)

/-- Paper: Lemma 10.4.1.2, p. 456. The spectral projection of any representative
is the unique orthogonal representative, canonically isometric to the quotient
via Mathlib's quotient equivalence. -/
theorem spectralQuotient_orthogonalRepresentative (_ha : 0 < a) (u : W₀) :
    let v := (Θ₀).quotientEquivOrthogonal (Qₐ u)
    (v : W₀) = Pspec u ∧
      ∀ w : (Θ₀).orthogonal, Qₐ w = Qₐ u → w = v := by
  intro v
  have hu : Qₐ u = Qₐ (Pspec u) := (Submodule.Quotient.eq (Θ₀)).2 (by
    have h : u - Pspec u = (Θ₀).starProjection u :=
      sub_eq_of_eq_add ((Θ₀).starProjection_add_starProjection_orthogonal u).symm
    exact (congrArg (· ∈ Θ₀) h).mpr ((Θ₀).starProjection_apply_mem u))
  have hv : v = ⟨Pspec u, (Θ₀).orthogonal.starProjection_apply_mem u⟩ :=
    (congrArg (Θ₀).quotientEquivOrthogonal hu).trans
      ((Θ₀).quotientEquivOrthogonal_mk _ ((Θ₀).orthogonal.starProjection_apply_mem u))
  exact ⟨congrArg Subtype.val hv, fun w hw ↦
    ((Θ₀).quotientEquivOrthogonal_mk (w : W₀) w.2).symm.trans
      (congrArg (Θ₀).quotientEquivOrthogonal hw)⟩

variable {Λ ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}
local notation "innerBand" => (0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)

/-- Paper: Definition 10.4.1.3(1), p. 457. Geometric truncation first projects
onto theta and then multiplies by the cutoff.
Deviation: The cutoff is real as in Definition 9.3.3.1 in Lean. The operator is
defined whenever the cutoff exists, including outside the stated inner-band condition. -/
def geometricTruncation (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp Pgeom

/-- Paper: Definition 10.4.1.3(1), p. 457. The geometric truncation of
convolution applies the geometric truncation operator after convolution. -/
def geometricTruncatedConvolution (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    W₀ →L[ℂ] W₀ :=
  (geometricTruncation a hα hs hρ).comp (A(φ))

/-- Paper: Definition 10.4.1.3(2), p. 457. Spectral truncation first projects
onto the orthogonal complement of theta and then multiplies by the cutoff.
Deviation: As for geometric truncation, a real cutoff suffices to define the operator. -/
def spectralTruncation (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp Pspec

/-- Paper: Definition 10.4.1.3(2), p. 457. The spectral truncation of
convolution applies the spectral truncation operator after convolution. -/
def spectralTruncatedConvolution (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    W₀ →L[ℂ] W₀ :=
  (spectralTruncation a hα hs hρ).comp (A(φ))

/-- Paper: Definition 10.4.1.3(1), p. 457. On the theta subspace, geometric
truncation acts by multiplication by the cutoff. -/
theorem geometricTruncation_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) {u : W₀} (_hu : u ∈ Θ₀) :
    geometricTruncation a hα hs hρ u = M(hρ) u :=
  w18_comp_apply_of_fix _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.3(2), p. 457. On the orthogonal complement of
theta, spectral truncation acts by multiplication by the cutoff. -/
theorem spectralTruncation_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) {u : W₀} (_hu : u ∈ (Θ₀).orthogonal) :
    spectralTruncation a hα hs hρ u = M(hρ) u :=
  w18_comp_apply_of_fix _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.3(1), p. 457. If an input's convolution belongs
to theta, its geometric truncated convolution is just cutoff multiplication of the result. -/
theorem geometricTruncatedConvolution_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : A(φ) u ∈ Θ₀) :
    geometricTruncatedConvolution a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.3(2), p. 457. If an input's convolution is
orthogonal to theta, its spectral truncated convolution is cutoff multiplication of the result. -/
theorem spectralTruncatedConvolution_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : A(φ) u ∈ (Θ₀).orthogonal) :
    spectralTruncatedConvolution a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Remark 10.4.1.4, p. 457. The two truncation operators add up to
multiplication by the common cutoff. -/
theorem geometricTruncation_add_spectralTruncation (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) :
    geometricTruncation a hα hs hρ + spectralTruncation a hα hs hρ = M(hρ) :=
  w18_comp_add_comp _ _ _ fun u ↦ Submodule.starProjection_add_starProjection_orthogonal u

/-- Paper: Remark 10.4.1.4, p. 457. For the singleton base and positive even
degree the translation operators are unbounded in operator norm along powers
of a class of logarithmic norm one.
Deviation: Polynomial growth in both directions and unboundedness of the
operator norms rule out the asserted equivalent conformal Hilbert norm. -/
theorem hardySobolevTranslation_zeroBase_powers_unbounded (n : ℕ) (_hn : 0 < n)
    (g : C𝔽) (_hg : logNorm g = 1) :
    ∀ C : ℝ, ∃ k : ℕ, C <
      ‖hardySobolevTranslation μ𝔽 m𝔽 0 0 (2 * (n : ℝ)) le_rfl
        (mul_nonneg zero_le_two (Nat.cast_nonneg n)) (g ^ k)‖ := by sorry

/-- Paper: Remark 10.4.1.4, p. 457. By invariance of theta, an output
geometric projection has no effect after convolution of a geometric vector. -/
theorem geometricProjection_convolution_geometricProjection (φ : BruhatCompactSupport C𝔽) :
    (Pgeom).comp ((A(φ)).comp Pgeom) = (A(φ)).comp Pgeom := by
  apply ContinuousLinearMap.ext
  intro u
  apply geometricProjection_apply_of_mem a hα hs
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ
    ((Θ₀).starProjection_apply_mem u)

/-- Paper: Remark 10.4.1.4, p. 458. Spectral projection after convolution
depends only on the input's spectral projection. -/
theorem spectralProjection_convolution_spectralProjection (φ : BruhatCompactSupport C𝔽) :
    (Pspec).comp ((A(φ)).comp Pspec) = (Pspec).comp (A(φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  let L := (Pspec).comp (A(φ))
  have hz : L (Pgeom u) = 0 := by
    apply Submodule.starProjection_orthogonal_apply_eq_zero
    apply (Submodule.Quotient.mk_eq_zero (Θ₀)).mp
    exact hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ
      ((Θ₀).starProjection_apply_mem u)
  calc
    L (Pspec u) = 0 + L (Pspec u) := (zero_add _).symm
    _ = L (Pgeom u) + L (Pspec u) := congrArg (fun v : W₀ ↦ v + L (Pspec u)) hz.symm
    _ = L (Pgeom u + Pspec u) := (map_add L _ _).symm
    _ = L u := congrArg L ((Θ₀).starProjection_add_starProjection_orthogonal u)

/-- Paper: Remark 10.4.1.4, p. 458. There is no convolution block from
the geometric subspace to the spectral subspace. -/
theorem spectralProjection_convolution_geometricProjection (φ : BruhatCompactSupport C𝔽) :
    (Pspec).comp ((A(φ)).comp Pgeom) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Submodule.starProjection_orthogonal_apply_eq_zero
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ
    ((Θ₀).starProjection_apply_mem u)

-- The reverse off-diagonal block on p. 458 can be nonzero. Its nonvanishing
-- cannot be universal in the test function, since the zero test kills every block.
-- The quotient action on the orthogonal complement is transported by its
-- isometry. Ambient translation on the complement would require invariance.

/-- Paper: Definition 10.4.1.5(1), p. 458. The geometric restriction applies
geometric projection, then convolution, then the cutoff multiplier. -/
def geometricRestriction (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp ((A(φ)).comp Pgeom)

/-- Paper: Definition 10.4.1.5(2), p. 458. The spectral restriction applies
spectral projection, then convolution, then the cutoff multiplier. -/
def spectralRestriction (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp ((A(φ)).comp Pspec)

/-- Paper: Definition 10.4.1.5(1), p. 458. On a geometric vector, the geometric
restriction is convolution followed by cutoff multiplication. -/
theorem geometricRestriction_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : u ∈ Θ₀) :
    geometricRestriction a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix' _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.5(2), p. 458. On a spectral vector, the spectral
restriction is convolution followed by cutoff multiplication. -/
theorem spectralRestriction_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : u ∈ (Θ₀).orthogonal) :
    spectralRestriction a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix' _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: (10.4.2.1), p. 458. Cutoff convolution is the sum of its geometric
and spectral truncations.
Deviation: The printed left-hand side has a stray trace, while the equation
has operators on the right-hand side. -/
theorem truncatedConvolution_eq_geometric_add_spectral (hρ : IsModulatedCutoff m𝔽 Λ ε ρ)
    (φ : BruhatCompactSupport C𝔽) :
    (M(hρ)).comp (A(φ)) =
      geometricTruncatedConvolution a hα hs hρ φ + spectralTruncatedConvolution a hα hs hρ φ :=
  by
  apply ContinuousLinearMap.ext
  intro u
  exact (DFunLike.congr_fun (geometricTruncation_add_spectralTruncation (F := F) a hα hs hρ)
    (A(φ) u)).symm

/-- Paper: (10.4.2.5), p. 459. Spectral projection after convolution is quotient
convolution transported back along the isometric section of the quotient map. -/
theorem spectralProjection_convolution_factor (φ : BruhatCompactSupport C𝔽) :
    (Pspec).comp (A(φ)) = ((Θ₀).orthogonal.subtypeL).comp
      ((Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Aₛ(φ)).comp Qₐ)) := by
  let sectionMap : H₀ → W₀ := fun x ↦ ((Θ₀).quotientEquivOrthogonal x).val
  have proj (w : W₀) : Pspec w = sectionMap ((Θ₀).mkQ w) := by
    have hzero : (Θ₀).mkQ (Pgeom w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ((Θ₀).starProjection_apply_mem w)
    have hsame : (Θ₀).mkQ w = (Θ₀).mkQ (Pspec w) := calc
      _ = (Θ₀).mkQ (Pgeom w + Pspec w) :=
        congrArg (Θ₀).mkQ ((Θ₀).starProjection_add_starProjection_orthogonal w).symm
      _ = _ := (map_add (Θ₀).mkQ _ _).trans (by rw [hzero, zero_add])
    have hrep := (Θ₀).quotientEquivOrthogonal_mk (Pspec w) ((Θ₀).orthogonal.starProjection_apply_mem w)
    exact (congrArg Subtype.val hrep).symm.trans (congrArg sectionMap hsame.symm)
  apply ContinuousLinearMap.ext
  intro u
  exact (proj (A(φ) u)).trans (congrArg sectionMap
    (spectralConvolution_mkQ (F := F) a (hStrip(hα)) hs φ u).symm)

-- TODO(paper-gap): The printed unconditional assertion for 0 ≤ s ≤ 1 needs
-- quotient nuclearity in that range. By (10.4.2.5) and Qₐ Sₐ = Id,
-- quotient nuclearity is equivalent to nuclearity of Pspec after convolution.

/-- Paper: Theorem 10.4.2.1, p. 459. The untruncated spectral projection
after convolution is nuclear.
Deviation: Quotient nuclearity is explicit so the theorem applies at every
nonnegative degree where this input holds. Section 10.3 states it for s > 1. Its proof is subject to ERRATA R5. -/
theorem spectralProjection_convolution_nuclear (φ : BruhatCompactSupport C𝔽)
    (_hquot : quotientNuclear(φ)) :
    IsNuclearOperator ((Pspec).comp (A(φ))) := by
  rw [spectralProjection_convolution_factor]
  let e := (Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv
  exact isNuclearOperator_comp_comp _hquot Qₐ ((Θ₀).orthogonal.subtypeL.comp e.toContinuousLinearMap)
    (Subtype.val_injective.comp e.injective)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral truncation of convolution is nuclear.
Deviation: Quotient nuclearity is explicit, as for the untruncated operator. -/
theorem spectralTruncatedConvolution_nuclear (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    (_hquot : quotientNuclear(φ)) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) := by
  exact mul_mem_nuclearEndomorphisms_left (M(hρ))
    ⟨(Pspec).comp (A(φ)), spectralProjection_convolution_nuclear a hα hs φ _hquot⟩

/-- Paper: Theorem 10.4.2.1, p. 459. Geometric truncation of convolution is nuclear.
Deviation: Quotient nuclearity is explicit, as for spectral truncation. -/
theorem geometricTruncatedConvolution_nuclear (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand)
    (φ : BruhatCompactSupport C𝔽) (_hquot : quotientNuclear(φ)) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Function.Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hT, _, _⟩ := truncatedHardySobolevConvolution_trace μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ.val
    hc.aemeasurable φ.property.2 hb hm hsur hφs hρ _hband
  have hconv := hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ hc.aemeasurable hb
  let T : W₀ →L[ℂ] W₀ := (M(hρ)).comp (A(φ))
  have hn : T ∈ nuclearEndomorphisms W₀ :=
    (congrArg (fun U : W₀ →L[ℂ] W₀ ↦ IsNuclearOperator (E := W₀) (F := W₀) ((M(hρ)).comp U)) hconv).mp hT
  let S : nuclearEndomorphisms W₀ := ⟨_, spectralTruncatedConvolution_nuclear a hα hs hρ φ _hquot⟩
  have heq := truncatedConvolution_eq_geometric_add_spectral (F := F) a hα hs hρ φ
  have hdiff : geometricTruncatedConvolution a hα hs hρ φ = T - S.val :=
    eq_sub_of_add_eq heq.symm
  exact (congrArg (fun U : W₀ →L[ℂ] W₀ ↦ IsNuclearOperator U) hdiff).mpr
    ((nuclearEndomorphisms W₀).sub_mem hn S.property)

/-- Paper: Theorem 10.4.2.1, p. 459. The nuclear trace of cutoff convolution
splits as the sum of the geometric and spectral traces.
Deviation: Quotient nuclearity is explicit, and the trace identity includes
witnesses of nuclearity for all three operators. -/
theorem truncatedConvolution_trace_split (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand)
    (φ : BruhatCompactSupport C𝔽) (_hquot : quotientNuclear(φ)) :
    let T := (M(hρ)).comp (A(φ))
    let G := geometricTruncatedConvolution a hα hs hρ φ
    let S := spectralTruncatedConvolution a hα hs hρ φ
    ∃ (hT : IsNuclearOperator T) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S),
      hilbertTrace (H := W₀) ⟨T, hT⟩ =
        hilbertTrace (H := W₀) ⟨G, hG⟩ + hilbertTrace (H := W₀) ⟨S, hS⟩ := by
  intro T G S
  have heq : T = G + S := truncatedConvolution_eq_geometric_add_spectral (F := F) a hα hs hρ φ
  have hG : IsNuclearOperator G := geometricTruncatedConvolution_nuclear (F := F) a hα hs hρ _hband φ _hquot
  have hS : IsNuclearOperator S := spectralTruncatedConvolution_nuclear (F := F) a hα hs hρ φ _hquot
  clear_value T G S
  have addTrace {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T G S : H →L[ℂ] H) (heq : T = G + S) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S) :
      ∃ (hT : IsNuclearOperator T) (hg : IsNuclearOperator G) (hs' : IsNuclearOperator S),
        hilbertTrace (H := H) ⟨T, hT⟩ = hilbertTrace (H := H) ⟨G, hg⟩ + hilbertTrace (H := H) ⟨S, hs'⟩ := by
    subst T
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let g : nuclearEndomorphisms H := ⟨G, hG⟩
    let s' : nuclearEndomorphisms H := ⟨S, hS⟩
    refine ⟨(g + s').property, hG, hS, ?_⟩
    exact (hL (g + s')).symm.trans ((L.map_add g s').trans (congrArg₂ (· + ·) (hL g) (hL s')))
  exact addTrace (H := ↥W₀) T G S heq hG hS

/-- Paper: Theorem 10.4.2.2, p. 460. As the cutoff radius tends to infinity
with width times radius tending to zero, the trace of projection after
convolution tends to the quotient convolution trace.
Deviation: Quotient nuclearity is explicit. The quotient trace on a general
strip is the one in Theorem 10.3.2.1, with Theorem 10.3.1.1 for the line. -/
theorem spectralTruncatedConvolution_trace_tendsto (φ : BruhatCompactSupport C𝔽)
    (hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        let T := spectralTruncatedConvolution a hα hs hcut φ
        ∃ hT : IsNuclearOperator T, traces R = hilbertTrace (H := W₀) ⟨T, hT⟩) ∧
      Tendsto traces atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)) := by sorry

/-- Paper: Remark 10.4.2.3, p. 460. Subtracting the geometric truncated
trace from the logarithmic main term gives the quotient trace in the cutoff limit.
Deviation: The norm-one mass is the Tamagawa mass from Appendix A and
quotient nuclearity is explicit. -/
theorem geometricTruncatedConvolution_trace_remainder_tendsto (φ : BruhatCompactSupport C𝔽)
    (hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        let T := geometricTruncatedConvolution a hα hs hcut φ
        ∃ hT : IsNuclearOperator T, traces R = hilbertTrace (H := W₀) ⟨T, hT⟩) ∧
      Tendsto (fun R ↦
        ((2 * Real.log R * (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ) *
          φ.val 1 - traces R) atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)) := by sorry

/-- Paper: Proposition 10.4.2.4, p. 460. For degree at least three the trace of
untruncated spectral projection after convolution equals the quotient trace.
Both operators are nuclear. -/
theorem spectralProjection_convolution_trace (_hs3 : 3 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    ∃ (hT : IsNuclearOperator ((Pspec).comp (A(φ)))) (hquot : quotientNuclear(φ)),
      hilbertTrace (H := W₀) ⟨(Pspec).comp (A(φ)), hT⟩ =
        hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩ := by sorry

local notation "closedSpan(" u ")" => (Submodule.span ℂ (Set.range u)).topologicalClosure

section ApproximateLifts

variable {ι : Type*} [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (E₀ V : Submodule ℂ E) [IsClosed (E₀ : Set E)]

/-- Paper: Lemma 10.4.2.5, p. 461. Biorthogonal quotient vectors lying in the
image of V admit lifts in V in the enlarged norm collar. Their coefficient
functionals are pulled back along the quotient map.
Deviation: This records the biorthogonal lift and the norm bounds. The claimed
Schauder conclusion fails even for Schauder input in Banach spaces. The caller
chooses the tolerance, as in (10.4.2.24). The strict collar and arbitrary index
type also cover the finite and empty families of §10.2. -/
theorem exists_biorthogonalBasisLift (x : ι → E ⧸ E₀) (f : ι → StrongDual ℂ (E ⧸ E₀))
    (_hbio : ∀ m n, f m (x n) = if m = n then 1 else 0)
    (r r' ε : ℝ) (_hr : 0 < r) (_hr' : 0 < r') (_hε : 0 < ε) (_hεr : ε < r)
    (_hcollar : ∀ m, ‖x m‖ ∈ Icc r r')
    (_hdense : E₀ ≤ (V ⊓ E₀).topologicalClosure) (_himage : ∀ m, x m ∈ V.map E₀.mkQ) :
    ∃ u : ι → E,
      (∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧ ‖u m‖ ∈ Ioo (r - ε) (r' + ε)) ∧
      ∀ m n, f m (E₀.mkQ (u n)) = if m = n then 1 else 0 := by
  classical
  have lift (m : ι) : ∃ u : E, u ∈ V ∧ E₀.mkQ u = x m ∧ ‖u‖ ∈ Ioo (r - ε) (r' + ε) := by
    obtain ⟨v, hv, hqv⟩ := _himage m
    obtain ⟨z, hz, hn⟩ := Submodule.Quotient.norm_mk_lt (x m) (half_pos _hε)
    have hdiff : v - z ∈ E₀ := (Submodule.Quotient.mk_eq_zero _).mp (by
      change E₀.mkQ (v - z) = 0
      rw [map_sub, hqv, show E₀.mkQ z = x m from hz, sub_self])
    obtain ⟨d, hd, hdist⟩ := Metric.mem_closure_iff.mp (_hdense hdiff) (ε / 2) (half_pos _hε)
    have hqd : E₀.mkQ d = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hd.2
    have hqu : E₀.mkQ (v - d) = x m := by rw [map_sub, hqv, hqd, sub_zero]
    refine ⟨v - d, V.sub_mem hv hd.1, hqu, ?_, ?_⟩
    · have hu := Submodule.Quotient.norm_mk_le E₀ (v - d)
      change ‖E₀.mkQ (v - d)‖ ≤ _ at hu
      rw [hqu] at hu
      linarith [(_hcollar m).1]
    · rw [dist_eq_norm] at hdist
      have heq : v - d = z + (v - z - d) := by abel
      rw [heq]
      linarith [norm_add_le z (v - z - d), (_hcollar m).2]
  choose u hu using lift
  exact ⟨u, hu, fun m n ↦ (congrArg (f m) (hu n).2.1).trans (_hbio m n)⟩

/-- Paper: Lemma 10.4.2.5, p. 461. Lifts can be chosen to remain inside the
enlarged collar under sufficiently small kernel perturbations. Each perturbed
family has canonically isomorphic closed span via the assignment on its generators.
Deviation: The perturbation conclusion uses biorthogonality and exact quotient
lifts, with no general Schauder claim. -/
theorem exists_biorthogonalBasisLift_stable [Countable ι] (x : ι → E ⧸ E₀)
    (f : ι → StrongDual ℂ (E ⧸ E₀))
    (_hbio : ∀ m n, f m (x n) = if m = n then 1 else 0)
    (r r' ε : ℝ) (_hr : 0 < r) (_hr' : 0 < r') (_hε : 0 < ε) (_hεr : ε < r)
    (_hcollar : ∀ m, ‖x m‖ ∈ Icc r r')
    (_hdense : E₀ ≤ (V ⊓ E₀).topologicalClosure) (_himage : ∀ m, x m ∈ V.map E₀.mkQ) :
    ∃ (u : ι → E) (δ : ι → ℝ), (∀ m, 0 < δ m) ∧
      (∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧ ‖u m‖ ∈ Ioo (r - ε) (r' + ε)) ∧
      ∀ y : ι → E, (∀ m, y m ∈ V ⊓ E₀ ∧ ‖y m‖ < δ m) →
        (∀ m, u m + y m ∈ V ∧ E₀.mkQ (u m + y m) = x m ∧
          ‖u m + y m‖ ∈ Ioo (r - ε) (r' + ε)) ∧
        ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
          ∀ (v : closedSpan(u)) (m : ι), v.val = u m → (T v).val = u m + y m := by sorry

/-- Paper: Terminology 10.4.2.1, p. 462. An ε-lift lies in the specified
subspace, represents the given quotient vectors, has the prescribed pulled-back
coefficient values, and stays in the enlarged norm collar.
Deviation: Exact representation is explicit. Totality gives it from the
coefficient equations for the bases in the paper. -/
def IsEpsilonBasisLift (x : ι → E ⧸ E₀) (f : ι → StrongDual ℂ (E ⧸ E₀))
    (r r' ε : ℝ) (u : ι → E) : Prop :=
  0 < ε ∧ ε < r ∧ (∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧ ‖u m‖ ∈ Icc (r - ε) (r' + ε)) ∧
    ∀ m n, f m (E₀.mkQ (u n)) = if m = n then 1 else 0

/-- Paper: Terminology 10.4.2.1, p. 462. A lift of a biorthogonal family with
the required collar bounds satisfies the ε-lift conditions. -/
theorem isEpsilonBasisLift_of_mkQ_eq (x : ι → E ⧸ E₀) (f : ι → StrongDual ℂ (E ⧸ E₀))
    (_hbio : ∀ m n, f m (x n) = if m = n then 1 else 0)
    {r r' ε : ℝ} (_hε : 0 < ε) (_hεr : ε < r)
    (u : ι → E) (_hu : ∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧
      ‖u m‖ ∈ Icc (r - ε) (r' + ε)) :
    IsEpsilonBasisLift E₀ V x f r r' ε u := by
  refine ⟨_hε, _hεr, _hu, fun m n ↦ ?_⟩
  exact (congrArg (f m) (_hu n).2.1).trans (_hbio m n)

/-- Paper: Remark 10.4.2.6, p. 463. The image of the open unit ball under
the quotient map is exactly the open unit ball in the quotient norm. -/
theorem quotient_image_openUnitBall :
    E₀.mkQ '' Metric.ball 0 1 = Metric.ball 0 1 := by
  ext y
  simp only [Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Submodule.Quotient.norm_mk_le E₀ x).trans_lt hx
  · intro hy
    obtain ⟨x, hxy, hx⟩ := Submodule.Quotient.norm_mk_lt y (sub_pos.mpr hy)
    exact ⟨x, by linarith, hxy⟩

/-- Paper: Remark 10.4.2.6, p. 463. In a reflexive Banach space the quotient
map also takes the closed unit ball onto the closed unit ball. -/
theorem quotient_image_closedUnitBall_of_reflexive
    (_hE : Surjective (NormedSpace.inclusionInDoubleDual ℂ E)) :
    E₀.mkQ '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by sorry

-- The Schauder conclusion of Lemma 10.4.2.5 is false even for a Schauder
-- quotient basis. See the convergent-sequence example in the printed file.
-- The upper bound r' - ε/2 in the proof on p. 462 should be r' + ε/2.
-- The Hilbert-space repair below uses exact image membership.

end ApproximateLifts

/-- Paper: Remark 10.4.2.7, p. 463. In a Hilbert space, collar lifts in V
can be chosen so that their closed span is isomorphic to the orthogonal
complement of the kernel.
Deviation: The quotient basis vectors are required to lie in the exact
image of V as in Lemma 10.4.2.5. The perturbations use the same chosen lift. -/
theorem exists_hilbertBasisLift_closedSpan_equiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (E₀ V : Submodule ℂ E) [IsClosed (E₀ : Set E)]
    (b : _root_.SchauderBasis ℂ (E ⧸ E₀)) (r r' : ℝ) (_hr : 0 < r) (_hr' : 0 < r')
    (_hcollar : ∀ m, ‖b m‖ ∈ Icc r r')
    (_hdense : E₀ ≤ (V ⊓ E₀).topologicalClosure) (_himage : ∀ m, b m ∈ V.map E₀.mkQ) :
    ∃ (u : ℕ → E) (ε : ℝ), IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε u ∧
      (∃ B : _root_.SchauderBasis ℂ (closedSpan(u)), ∀ m, (B m).val = u m) ∧
      Nonempty (closedSpan(u) ≃L[ℂ] E₀.orthogonal) ∧
      ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧
        ∀ y : ℕ → E, (∀ m, y m ∈ V ⊓ E₀ ∧ ‖y m‖ < δ m) →
          IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε (fun m ↦ u m + y m) ∧
          ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
            ∀ (v : closedSpan(u)) (m : ℕ), v.val = u m → (T v).val = u m + y m := by sorry

/-- Paper: Theorem 10.4.2.8, p. 463. At each admissible cutoff, the operator
obtained by spectral projection, convolution and cutoff is nuclear. -/
theorem spectralRestriction_nuclear (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand)
    (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralRestriction a hα hs hρ φ) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Function.Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hT, _, _⟩ := truncatedHardySobolevConvolution_trace μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ.val
    hc.aemeasurable φ.property.2 hb hm hsur hφs hρ _hband
  have hconv := hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ hc.aemeasurable hb
  have hn : IsNuclearOperator ((M(hρ)).comp (A(φ))) :=
    (congrArg (fun U : W₀ →L[ℂ] W₀ ↦ IsNuclearOperator ((M(hρ)).comp U)) hconv).mp hT
  exact mul_mem_nuclearEndomorphisms_right (H := W₀) Pspec ⟨_, hn⟩

-- In (10.4.2.21)–(10.4.2.24), use SpectralStripJetIndex and spectralZeroJet:
-- the zero is at a + b + it and the jet exponent is b + it. Proposition
-- 10.2.2.2 bounds dual jets. It gives no upper bound for the primal lifts,
-- and clustered ordinates obstruct such a bound on the critical line (R5).
-- The integral (10.4.2.26) is the squared rank-one norm. In (10.4.2.27)
-- one copy of each complex amplitude must be conjugated.

private theorem combine_trace_limits {p q : (ℝ → ℂ) → Prop} {z : ℂ}
    (hl : ∃ l, p l ∧ Tendsto l atTop (𝓝 z))
    (hd : ∀ l, p l → ∃ r, q r ∧ Tendsto (fun x ↦ r x - l x) atTop (𝓝 0)) :
    ∃ r, q r ∧ Tendsto r atTop (𝓝 z) := by
  obtain ⟨l, hl, hlim⟩ := hl
  obtain ⟨r, hr, hd⟩ := hd l hl
  exact ⟨r, hr, by simpa only [sub_add_cancel, zero_add] using hd.add hlim⟩

local notation "cutoffTraces(" op ", " eps ", " rho ", " test ", " t ")" =>
  (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R ((eps) R) ((rho) R),
    let T := (op) a hα hs hc (test)
    ∃ hT : IsNuclearOperator (E := W₀) (F := W₀) T, (t) R = hilbertTrace (H := W₀) ⟨T, hT⟩)

/-- Paper: Theorem 10.4.2.8, pp. 463–464. The trace of the cutoff times the
spectral-to-geometric block tends to zero. By (10.4.1.11) and linearity of
the trace this is the difference of the traces of the two composition orders.
Gap: Footnote 8 leaves this estimate open. Arbitrary collar lifts need not be
orthogonal representatives, and (10.4.2.34) gives no summable rank-one bound. -/
theorem spectralRestriction_offDiagonal_trace_tendsto_zero (φ : BruhatCompactSupport C𝔽)
    (_hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R)
    (l : ℝ → ℂ)
    (_hl : cutoffTraces(spectralTruncatedConvolution, ε, ρ, φ, l)) :
    ∃ r : ℝ → ℂ, cutoffTraces(spectralRestriction, ε, ρ, φ, r) ∧
      Tendsto (fun R ↦ r R - l R) atTop (𝓝 0) := by sorry

/-- Paper: Theorem 10.4.2.8, p. 463. As the cutoff radius tends to infinity
with width times radius tending to zero, the trace of convolution after
spectral projection tends to the quotient convolution trace.
Deviation: Quotient nuclearity is explicit. -/
theorem spectralRestriction_trace_tendsto (φ : BruhatCompactSupport C𝔽)
    (hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ traces : ℝ → ℂ, cutoffTraces(spectralRestriction, ε, ρ, φ, traces) ∧
      Tendsto traces atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)) :=
  combine_trace_limits
    (p := fun t ↦ cutoffTraces(spectralTruncatedConvolution, ε, ρ, φ, t))
    (q := fun t ↦ cutoffTraces(spectralRestriction, ε, ρ, φ, t))
    (z := hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)
    (spectralTruncatedConvolution_trace_tendsto (F := F) a hα hs φ hquot ε ρ _hε _hρ)
    (spectralRestriction_offDiagonal_trace_tendsto_zero (F := F) a hα hs φ hquot ε ρ _hε _hρ)

end Truncations

end RiemannMasullo
