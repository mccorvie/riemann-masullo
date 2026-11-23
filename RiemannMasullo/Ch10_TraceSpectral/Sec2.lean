module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Total
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Spectral Markushevich bases

Masullo, §10.2, pp. 438–447. The basis vectors in the negative spaces are
represented by functions modulo almost-everywhere equality.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "W'(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s true
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)

local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

section Quotients

/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. The denominator is the
closed subspace from §10.1, giving the canonical norm on the quotient. -/
instance instClosedSpectralThetaSec2 (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    IsClosed (Θ(a, hI, hs) : Set W(l, r, s)) :=
  Submodule.isClosed_topologicalClosure _

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The numerator of the
isotype quotient is a closed subspace of the ambient Hilbert space. -/
instance instClosedSpectralIsotypeSec2 {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (Wω(hI, hs, ω) : Set W(l, r, s)) :=
  isClosed_actionIsotype (ρ(l, r, s, hI, hs)) ω

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The isotype quotient
uses the closed intersection of the isotype with the theta subspace. -/
instance instClosedSpectralIsotypeThetaSec2 (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    IsClosed ((Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype : Set ↥(Wω(hI, hs, ω))) :=
  (instClosedSpectralThetaSec2 (F := F) a hI hs).preimage continuous_subtype_val

variable (F) in
/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. Divide the weighted
Sobolev space by the closure of the weighted polar-free theta functions.
Deviation: The line uses the compact interval with both endpoints zero, as in §9.2.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev spectralSobolevQuotient (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :=
  W(l, r, s) ⧸ Θ(a, hI, hs)

/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. A Sobolev vector has
zero spectral class exactly when it is in the closed weighted theta subspace. -/
theorem spectralSobolevQuotient_eq_zero (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (f : W(l, r, s)) : Θ(a, hI, hs).mkQ f = 0 ↔ f ∈ Θ(a, hI, hs) :=
  Submodule.Quotient.mk_eq_zero _

variable (F) in
/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. Divide the ambient
norm-one isotype by its closed weighted theta subspace.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev spectralSobolevIsotypeQuotient (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :=
  ↥(Wω(hI, hs, ω)) ⧸ (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The isotype quotient
maps isometrically onto the isotype of the full quotient by inclusion of
representatives. The isotype action is the restriction of the continuous
idele class group action on that quotient. -/
theorem spectralSobolevIsotypeQuotient_isometry (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let N := Θ(a, hI, hs)
    let Q := spectralSobolevQuotient F a hI hs
    let E := Wω(hI, hs, ω)
    ∃ ρQ : C𝔽 →* (Q →L[ℂ] Q),
      (∀ (g : C𝔽) (f : W(l, r, s)),
        ρQ g (N.mkQ f) = N.mkQ (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs g f)) ∧
      Continuous (fun p : C𝔽 × Q ↦ ρQ p.1 p.2) ∧
      ∃ U : spectralSobolevIsotypeQuotient F a hI hs ω ≃ₗᵢ[ℂ]
          actionIsotype (ρQ.comp (ideleClassNorm F).ker.subtype) ω,
        ∀ f : E, (U ((N.comap E.subtype).mkQ f) : Q) = N.mkQ f.val := by sorry

/-- Paper: (10.2.1.3), pp. 439–440, and (10.2.2.3), p. 445. The Sobolev
duality evaluates the unweighted bilinear product integral. -/
def spectralSobolevPairing {l r s : ℝ} (f : W(l, r, s)) (u : W'(l, r, s)) : ℂ :=
  ∫ g, f g * u g ∂μ𝔽

local notation "pair(" f ", " u ")" => spectralSobolevPairing (F := F) f u

local notation "T(" l ", " r ", " s ", " hI ", " hs ")" =>
  (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 l r s hI hs).exists.choose

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. The pairing is
integrable and evaluates the ambient strong dual under its Sobolev isometry. -/
theorem spectralSobolevPairing_dual {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (Λ : StrongDual ℂ W(l, r, s)) (f : W(l, r, s)) :
    let T := T(l, r, s, hI, hs)
    Integrable (fun g ↦ f g * T Λ g) μ𝔽 ∧ Λ f = pair(f, T Λ) := by
  exact (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 l r s hI hs).exists.choose_spec Λ f

/-- Conjugating a weighted L² vector and multiplying by the density gives a vector of the
reciprocal-weight space whose product integral with the original is its squared norm. -/
private theorem spectralSobolevPairing_isotype_conj {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ ρ' : X → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ') (hpos : ∀ x, 0 < ρ x)
    (hpos' : ∀ x, 0 < ρ' x) (hr : ∀ x, ρ x * ρ' x = 1)
    (f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x))) :
    ∃ g : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)),
      (g : X → ℂ) =ᵐ[ν] (fun x ↦ (ρ x : ℂ) * star (f x)) ∧
      ∫ x, f x * g x ∂ν = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
  have hbase {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) :
      ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let u : X → ℂ := fun x ↦ (ρ x : ℂ) * star (f x)
  have hsq (x : X) : ‖u x‖ ^ 2 * ρ' x = ‖f x‖ ^ 2 * ρ x := by
    calc
      _ = ‖f x‖ ^ 2 * (ρ x * (ρ x * ρ' x)) := by
        dsimp only [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos x), norm_star]
        ring
      _ = _ := by rw [hr, mul_one]
  have hmeas : AEStronglyMeasurable u (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) :=
    (Complex.measurable_ofReal.comp hρ).aestronglyMeasurable.mul
      (((Lp.aestronglyMeasurable f).mono_ac (hbase hρ hpos)).mono_ac
        (withDensity_absolutelyContinuous _ _)).star
  have hmem : MemLp u 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    apply (integrable_withDensity_iff hρ'.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine (weightedL2_norm_eq ν hρ hpos f).1.congr (ae_of_all _ fun x ↦ ?_)
    change ‖f x‖ ^ 2 * ρ x = ‖u x‖ ^ 2 * (ENNReal.ofReal (ρ' x)).toReal
    rw [ENNReal.toReal_ofReal (hpos' x).le, hsq]
  have hcoe : (hmem.toLp u : X → ℂ) =ᵐ[ν] u := (hbase hρ' hpos').ae_eq hmem.coeFn_toLp
  refine ⟨hmem.toLp u, hcoe, ?_⟩
  obtain ⟨hint, hnorm⟩ := weightedL2_norm_eq ν hρ hpos f
  have hI : ∫ x, ‖f x‖ ^ 2 * ρ x ∂ν = ‖f‖ ^ 2 := by
    rw [hnorm, Real.sq_sqrt (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (hpos x).le)]
  rw [← hI, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  rw [hx]
  dsimp only [u]
  rw [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
  ring

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. The pairing on a
positive Sobolev isotype and the conjugate reciprocal-weight isotype is nondegenerate.
The negative-space isotype is specified by left translation of its representatives. -/
theorem spectralSobolevPairing_isotype {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    let IsConjugate (u : W'(l, r, s)) :=
      ∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g
    (∀ f : Wω(hI, hs, ω), f ≠ 0 →
      ∃ u : W'(l, r, s), IsConjugate u ∧ pair(f.val, u) ≠ 0) ∧
    ∀ u : W'(l, r, s), IsConjugate u → u ≠ 0 →
      ∃ f : Wω(hI, hs, ω), pair(f.val, u) ≠ 0 := by
  intro IsConjugate
  let w : C𝔽 → ℝ := fun g ↦ intervalSobolevDensity l r s (logNorm g)
  have hlog : Measurable logNorm :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hw : Measurable w := (continuous_intervalSobolevDensity' l r s).measurable.comp hlog
  have hwpos : ∀ x, 0 < w x := fun x ↦ intervalSobolevDensity_pos l r s _
  have hwk : ∀ (k : C₁) g, w (k.val⁻¹ * g) = w g := by
    intro k g
    have hk : ideleClassNorm F k.val = 1 := k.2
    simp only [w, map_mul, map_inv, hk, inv_one, one_mul]
  have hbase : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (w x)) :=
    withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hwpos x)).ne')
  have hwd : ((μ𝔽).withDensity fun x ↦ ENNReal.ofReal (w x)) ≪ μ𝔽 :=
    withDensity_absolutelyContinuous _ _
  have hiso (f : W(l, r, s)) : f ∈ Wω(hI, hs, ω) ↔
      ∀ k : C₁, (fun g ↦ f (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω k : ℂ) * f g := by
    rw [mem_actionIsotype]
    refine forall_congr' fun k ↦ ?_
    have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 l r s hI hs k.val f
    have hsm := hbase.ae_eq (Lp.coeFn_smul (ω k : ℂ) f)
    change hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs k.val f = (ω k : ℂ) • f ↔ _
    constructor
    · intro h
      rw [h] at htr
      exact htr.symm.trans hsm
    · intro h
      exact Lp.ext (hwd.ae_eq (htr.trans (h.trans hsm.symm)))
  have hωinv (k : C₁) : ((ω⁻¹ k : Circle) : ℂ) = star (ω k : ℂ) := by
    rw [show ω⁻¹ k = (ω k)⁻¹ from rfl, Circle.coe_inv_eq_conj]
    rfl
  have hqmp (k : C₁) := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving
  refine ⟨fun f hf ↦ ?_, fun u hu hu0 ↦ ?_⟩
  · obtain ⟨u, hu, hpair⟩ : ∃ u : W'(l, r, s),
        (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (fun x ↦ (w x : ℂ) * star (f.val x)) ∧
        ∫ x, f.val x * u x ∂μ𝔽 = ((‖f.val‖ ^ 2 : ℝ) : ℂ) :=
      spectralSobolevPairing_isotype_conj μ𝔽 (ρ := w) (ρ' := fun x ↦ (w x)⁻¹) hw hw.inv hwpos
        (fun x ↦ inv_pos.2 (hwpos x)) (fun x ↦ mul_inv_cancel₀ (hwpos x).ne') f.val
    refine ⟨u, fun k ↦ ?_, ?_⟩
    · have hfk := (hiso f.val).1 f.2 k
      have hu' := (hqmp k).ae_eq_comp hu
      filter_upwards [hu', hfk, hu] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv]
      ring
    · change ∫ g, f.val g * u g ∂μ𝔽 ≠ 0
      rw [hpair]
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 fun h ↦ hf (Subtype.ext h))
  · have key : ∃ f : W(l, r, s),
        (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (fun x ↦ ((w x)⁻¹ : ℂ) * star (u x)) ∧
        ∫ x, u x * f x ∂μ𝔽 = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      obtain ⟨f, hf, hpair⟩ := spectralSobolevPairing_isotype_conj μ𝔽
        (ρ := fun x ↦ if true = true then (w x)⁻¹ else w x)
        (ρ' := fun x ↦ if false = true then (w x)⁻¹ else w x)
        (by simp only [↓reduceIte]; exact hw.inv)
        (by simpa using hw) (by simpa using fun x ↦ inv_pos.2 (hwpos x)) (by simpa using hwpos)
        (fun x ↦ by simpa using inv_mul_cancel₀ (hwpos x).ne') u
      refine ⟨f, ?_, ?_⟩
      · filter_upwards [hf] with x hx
        rw [hx]
        simp only [↓reduceIte, Complex.ofReal_inv]
      · exact hpair
    obtain ⟨f, hf, hpair⟩ := key
    refine ⟨⟨f, (hiso f).2 fun k ↦ ?_⟩, ?_⟩
    · have hf' := (hqmp k).ae_eq_comp hf
      filter_upwards [hf', hu k, hf] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv, star_star]
      ring
    · change ∫ g, f g * u g ∂μ𝔽 ≠ 0
      simp_rw [mul_comm (f _)]
      rw [hpair]
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)

variable (F) in
/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pull a functional
back along the quotient map and realize it in the reciprocal-weight Sobolev space. -/
def spectralSobolevDualEmbedding (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    StrongDual ℂ (spectralSobolevQuotient F a hI hs) →ₗ[ℂ] W'(l, r, s) :=
  (T(l, r, s, hI, hs)).toLinearEquiv.toLinearMap.comp
    ((Θ(a, hI, hs)).mkQL.precomp ℂ).toLinearMap

/-- A Hilbert quotient dual maps isometrically to the annihilator under an ambient duality. -/
private theorem spectralSobolevDualEmbedding_isometry_range_hilbert
    {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (N : Submodule ℂ E) [IsClosed (N : Set E)]
    (T : StrongDual ℂ E ≃ₗᵢ[ℂ] V) (B : E → V → ℂ)
    (hB : ∀ (Λ : StrongDual ℂ E) (x : E), Λ x = B x (T Λ)) :
    Isometry (fun Λ : StrongDual ℂ (E ⧸ N) ↦ T (Λ.comp N.mkQL)) ∧
      Set.range (fun Λ : StrongDual ℂ (E ⧸ N) ↦ T (Λ.comp N.mkQL)) =
        {v : V | ∀ x ∈ N, B x v = 0} := by
  let P : StrongDual ℂ (E ⧸ N) →ₗ[ℂ] StrongDual ℂ E :=
    (N.mkQL.precomp ℂ).toLinearMap
  have hnorm (Λ : StrongDual ℂ (E ⧸ N)) : ‖P Λ‖ = ‖Λ‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ)
      intro x
      exact (Λ.le_opNorm (N.mkQL x)).trans
        (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le N x) (norm_nonneg Λ))
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (P Λ))
      intro q
      let v : Nᗮ := N.quotientEquivOrthogonal q
      have hv : N.mkQL v.val = q := by
        change (Submodule.Quotient.mk v.val : E ⧸ N) = q
        exact (N.quotientEquivOrthogonal_symm_eq_mk v.val v.property).symm.trans
          (N.quotientEquivOrthogonal.symm_apply_apply q)
      have hn : ‖v.val‖ = ‖q‖ := N.quotientEquivOrthogonal.norm_map q
      calc
        ‖Λ q‖ = ‖(P Λ) v.val‖ := by
          change ‖Λ q‖ = ‖Λ (N.mkQL v.val)‖
          rw [hv]
        _ ≤ ‖P Λ‖ * ‖v.val‖ := (P Λ).le_opNorm v.val
        _ = ‖P Λ‖ * ‖q‖ := by rw [hn]
  have hP : Isometry P := AddMonoidHomClass.isometry_of_norm P hnorm
  refine ⟨T.isometry.comp hP, ?_⟩
  ext v
  constructor
  · rintro ⟨Λ, rfl⟩ x hx
    rw [← hB (Λ.comp N.mkQL) x]
    change Λ (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero]
  · intro hv
    let φ : StrongDual ℂ E := T.symm v
    have hφ : N ≤ φ.ker := by
      intro x hx
      change φ x = 0
      rw [hB φ x]
      change B x (T (T.symm v)) = 0
      rw [T.apply_symm_apply]
      exact hv x hx
    refine ⟨N.liftQL φ hφ, ?_⟩
    have hcomp : (N.liftQL φ hφ).comp N.mkQL = φ := by
      ext x
      rfl
    change T ((N.liftQL φ hφ).comp N.mkQL) = v
    rw [hcomp]
    exact T.apply_symm_apply v

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pullback along the
quotient identifies its strong dual isometrically with the theta annihilator. -/
theorem spectralSobolevDualEmbedding_isometry_range (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) :
    let D := spectralSobolevDualEmbedding F a hI hs
    Isometry D ∧ range D = {u | ∀ f ∈ Θ(a, hI, hs), pair(f, u) = 0} := by
  exact spectralSobolevDualEmbedding_isometry_range_hilbert
    (E := W(l, r, s)) (V := W'(l, r, s))
    (Θ(a, hI, hs)) (T(l, r, s, hI, hs))
    (spectralSobolevPairing (F := F))
    (fun Λ f ↦ (spectralSobolevPairing_dual hI hs Λ f).2)

end Quotients

/-- Paper: Notation 10.2.1.1, p. 440, and Notation 10.2.2.1, p. 445.
Choose one continuous unitary extension for each norm-one character. -/
def IsSpectralBasepointChoice (χ : PontryaginDual C₁ → PontryaginDual C𝔽) : Prop :=
  ∀ ω, (χ ω).comp restriction = ω

/-- Paper: Notation 10.2.1.1, p. 440. A splitting of the idele class norm
provides unitary lifts for all the norm-one characters at once. -/
theorem exists_spectralBasepointChoice (F : Type*) [Field F] [NumberField F] :
    ∃ χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F),
      IsSpectralBasepointChoice χ := by
  let C := IdeleClassGroup (𝓞 F) F
  let n : C →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let q : IdeleGroup (𝓞 F) F →ₜ* C := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : Function.RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let P : C →ₜ* C := ContinuousMonoidHom.id C / σ.comp n
  have hP (x : C) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / σ (ideleClassNorm F x)) = 1
    rw [map_div, hσ, div_self']
  let r : C →ₜ* (ideleClassNorm F).ker := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  refine ⟨fun ω ↦ ω.comp r, fun ω ↦ ?_⟩
  ext x : 1
  change ω (r (x : C)) = ω x
  apply congrArg ω
  apply Subtype.ext
  change (x : C) / σ (ideleClassNorm F x) = x
  rw [show ideleClassNorm F (x : C) = 1 from x.property, map_one, div_one]

/-- Paper: (10.2.1.4), p. 440. In each component the norm twists of the
chosen extension give its unique complex parameter. -/
theorem IsSpectralBasepointChoice.existsUnique_normTwist
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} (_hχ : IsSpectralBasepointChoice χ)
    (ω : PontryaginDual C₁) (c : QuasiCharacter C𝔽)
    (_hc : ∀ g : C₁, c g.val = (ω g : ℂ)) :
    ∃! z : ℂ, c = ideleClassNormTwist (χ ω) z := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : Function.RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let d := c * j.comp (χ ω)⁻¹
  have hd (g : C𝔽) : d g = c g / (χ ω g : ℂ) := by
    change c g * (((χ ω g)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv, div_eq_mul_inv]
  have hk (g : C₁) : d g = 1 := by
    have hres : χ ω (g : C𝔽) = ω g := DFunLike.congr_fun (_hχ ω) g
    rw [hd, _hc g, hres, div_self (Circle.coe_ne_zero _)]
  obtain ⟨z, hz, huniq⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨z, ?_, fun w hw ↦ ?_⟩
  · ext g : 1
    let t := ideleClassNorm F g
    have hg : g / σ t ∈ (ideleClassNorm F).ker := by
      change ideleClassNorm F (g / σ t) = 1
      rw [map_div, hσ t, div_self']
    have hr : d g = (((t : ℝ≥0) : ℝ) : ℂ) ^ z := calc
      d g = d (g / σ t) * d (σ t) := by rw [← map_mul, div_mul_cancel]
      _ = _ := by rw [hk ⟨_, hg⟩, one_mul]; exact hz t
    change c g = (χ ω g : ℂ) * _
    exact ((div_eq_iff (Circle.coe_ne_zero _)).mp ((hd g).symm.trans hr)).trans (mul_comm _ _)
  · apply huniq
    intro t
    change d (σ t) = _
    rw [hd, hw]
    change ((χ ω (σ t) : ℂ) * (((ideleClassNorm F (σ t)).val : ℝ) : ℂ) ^ w) / _ = _
    rw [hσ t, mul_div_cancel_left₀ _ (Circle.coe_ne_zero _)]

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "vanishingOrder(" χ ", " z ")" =>
  meromorphicOrderAt (continuedCompletedHeckeL χ) z

/-- Paper: (10.2.1.5), p. 440, and (10.2.2.4), p. 446. A zero jet is the
chosen base character times the norm twist and a power of the log norm.
The line jet has real offset zero. -/
def spectralZeroJet (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) : ℂ :=
  ideleClassNormTwist χ (shift(b, t)) g * (logNorm g : ℂ) ^ k

/-- Paper: (10.2.1.5), p. 440, and (10.2.2.4), p. 446. The zeroth jet at
twist zero is the base character.
Deviation: Sanity check in degree and twist zero. -/
theorem spectralZeroJet_zero (χ : PontryaginDual C𝔽) (g : C𝔽) :
    spectralZeroJet χ 0 0 0 g = (χ g : ℂ) := by
  unfold spectralZeroJet
  simp only [pow_zero, mul_one, Complex.ofReal_zero, zero_mul, add_zero]
  change (χ g : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one]

/-- Paper: (10.2.1.6), p. 440, and (10.2.2.5), p. 446. Truncate the
multiplicity to the number of integrable jet orders at the boundary.
Deviation: Use the ceiling of (s−1)/2. The floor of (s−1)/2+1 admits the
logarithmically divergent endpoint when (s−1)/2 is an integer. -/
def spectralBoundaryMultiplicity (s : ℝ) (N : ℕ) : ℕ :=
  min N (Nat.ceil ((s - 1) / 2))

/-- Paper: (10.2.1.6), p. 440, and (10.2.2.5), p. 446. An order survives
the boundary cutoff exactly when it is below the zero multiplicity and strictly
below the reciprocal-weight integrability threshold.
Deviation: The limiting jet is excluded. -/
theorem lt_spectralBoundaryMultiplicity (s : ℝ) (N k : ℕ) :
    k < spectralBoundaryMultiplicity s N ↔ k < N ∧ (k : ℝ) < (s - 1) / 2 := by
  rw [spectralBoundaryMultiplicity, lt_min_iff, Nat.lt_ceil]

/-- Paper: Remark 10.2.1.2, pp. 440–441. A Markushevich system in the paper's
Hilbert setting is biorthogonal and both linear spans are norm dense.
Deviation: An arbitrary index type permits a finite or empty enumeration. -/
def IsSpectralMarkushevichBasis {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : ι → E) (Λ : ι → StrongDual ℂ E) : Prop :=
  (∀ i, Λ i (x i) = 1) ∧ (∀ i j, i ≠ j → Λ j (x i) = 0) ∧
    Dense (Submodule.span ℂ (range x) : Set E) ∧
    Dense (Submodule.span ℂ (range Λ) : Set (StrongDual ℂ E))

/-- Paper: Remark 10.2.1.2, p. 440. The dense functional family determines
its biorthogonal vectors uniquely. -/
theorem IsSpectralMarkushevichBasis.unique_vectors {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x y : ι → E} {Λ : ι → StrongDual ℂ E}
    (_hx : IsSpectralMarkushevichBasis x Λ) (_hy : IsSpectralMarkushevichBasis y Λ) :
    x = y := by
  funext i
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have he : ContinuousLinearMap.apply ℂ ℂ (x i) = ContinuousLinearMap.apply ℂ ℂ (y i) := by
    apply ContinuousLinearMap.ext_on _hx.2.2.2
    rintro _ ⟨j, rfl⟩
    change Λ j (x i) = Λ j (y i)
    by_cases hij : i = j
    · subst j
      exact (_hx.1 i).trans (_hy.1 i).symm
    · exact (_hx.2.1 i j hij).trans (_hy.2.1 i j hij).symm
  exact fun ℓ ↦ DFunLike.congr_fun he ℓ

local notation "multiplicity(" χ ", " z ")" => (vanishingOrder(χ, z)).untop₀.toNat

/-- Paper: Theorem 10.2.1.1, p. 440. Index the a-line jets by norm-one
characters, zero ordinates, and surviving derivative orders. Meromorphic order
excludes poles, even when the continuation has been assigned a value there.
Deviation: Apply the strict integrability cutoff of (10.2.1.6). -/
abbrev SpectralLineJetIndex (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a s : ℝ) :=
  {j : PontryaginDual C₁ × ℝ × ℕ //
    j.2.2 < spectralBoundaryMultiplicity s (multiplicity(χ j.1, shift(a, j.2.1)))}

/-- Paper: Theorem 10.2.1.1, p. 440. Every admitted a-line jet has positive
derivative capacity, so its indexing point is a zero of the completed L-function. -/
theorem SpectralLineJetIndex.order_pos {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a s : ℝ}
    (j : SpectralLineJetIndex χ a s) : 0 < vanishingOrder(χ j.val.1, shift(a, j.val.2.1)) := by
  have key : ∀ o : WithTop ℤ, 0 < o.untop₀.toNat → 0 < o := by
    intro o h
    cases o with
    | top => simp at h
    | coe n =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < n)
  have h := j.2
  unfold spectralBoundaryMultiplicity at h
  exact key _ (by omega)

local notation "lineJet(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) 0 (j).val.2.1 (j).val.2.2
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "L2μ'(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logNorm g))⁻¹)

-- On p. 443 an outside-band evaluation vanishes on the band image. Its
-- dual inner product with an inside-band evaluation can be nonzero:
-- for s = 2 on the rational trivial component the Gram kernel is
-- proportional to exp(-|t-u|). The claimed orthogonal adjoint range fails.

/-- A logarithmic power below the strict cutoff is square-integrable for the reciprocal weight. -/
private theorem spectralLineJet_memLp_of_norm_sq
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (s : ℝ) (k : ℕ)
    (hk : 2 * (k : ℝ) + 1 < s) (u : G → ℂ) (hu : Continuous u)
    (hnorm : ∀ g : G, ‖u g‖ ^ 2 = (Real.log ((m g).val : ℝ)) ^ (2 * k)) :
    MemLp u 2 (μ.withDensity fun g ↦
      ENNReal.ofReal (((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹)) := by
  let ν : Measure G := canonicalModulatedHaar m hm
  let : ν.IsHaarMeasure :=
    (existsUnique_canonicalModulatedHaar m hm).exists.choose_spec.1
  have hν : Integrable (fun g : G ↦ (Real.log ((m g).val : ℝ)) ^ (2 * k) *
      ((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹) ν :=
    (sobolev_log_preserving m hm hms).integrable_comp_of_integrable
      (integrable_pow_mul_rpow_inv hk)
  have hμ : Integrable (fun g : G ↦ (Real.log ((m g).val : ℝ)) ^ (2 * k) *
      ((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹) μ := by
    rw [Measure.isMulLeftInvariant_eq_smul μ ν]
    exact hν.smul_measure_nnreal
  have hρpos (g : G) : 0 < (1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hρ : Continuous (fun g : G ↦ (1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2)) :=
    ((continuous_const : Continuous (fun _ : G ↦ (1 : ℝ))).add
      ((continuous_logModule' m).pow 2)).rpow_const (fun g ↦ Or.inl (by
        change (1 : ℝ) + (Real.log ((m g).val : ℝ)) ^ 2 ≠ 0
        positivity))
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    (hρ.inv₀ (fun g ↦ (hρpos g).ne')).measurable.ennreal_ofReal
    (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ fun g ↦ ?_)
  dsimp only [Pi.inv_apply]
  rw [hnorm g, ENNReal.toReal_ofReal (inv_nonneg.mpr (hρpos g).le)]

/-- Paper: Theorem 10.2.1.1, p. 440. The admitted a-line jets are elements of
the reciprocal-weight Hilbert space.
Deviation: Exclude the divergent endpoint of (10.2.1.6). -/
theorem spectralLineJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (_hs : 1 < s) (j : SpectralLineJetIndex χ a s) :
    MemLp (lineJet(χ, j)) 2 (L2μ'(0, 0, s)) := by
  have horder : (j.val.2.2 : ℝ) < (s - 1) / 2 :=
    ((lt_spectralBoundaryMultiplicity s _ _).mp j.property).2
  have hk : 2 * (j.val.2.2 : ℝ) + 1 < s := by linarith
  let u : C𝔽 → ℂ := spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
  have hu : Continuous u :=
    (ideleClassNormTwist (χ j.val.1)
      ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I)).continuous.mul
      ((Complex.continuous_ofReal.comp (continuous_logModule' m𝔽)).pow j.val.2.2)
  have hnorm (g : C𝔽) : ‖u g‖ ^ 2 = (logNorm g) ^ (2 * j.val.2.2) := by
    have htwist : ‖ideleClassNormTwist (χ j.val.1)
        ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I) g‖ = 1 := by
      change ‖(χ j.val.1 g : ℂ) *
        (((ideleClassNorm F g).val : ℝ) : ℂ) ^
          ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I)‖ = 1
      rw [norm_mul, Circle.norm_coe, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos
          (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g)))]
      simp
    change ‖ideleClassNormTwist (χ j.val.1)
      ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I) g *
        (logNorm g : ℂ) ^ j.val.2.2‖ ^ 2 = _
    rw [norm_mul, htwist, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      (|logNorm g| ^ j.val.2.2) ^ 2 =
          (|logNorm g| ^ 2) ^ j.val.2.2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm j.val.2.2 2]
      _ = ((logNorm g) ^ 2) ^ j.val.2.2 :=
        congrArg (fun y : ℝ ↦ y ^ j.val.2.2) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * j.val.2.2) := (pow_mul _ _ _).symm
  have h := spectralLineJet_memLp_of_norm_sq m𝔽 hm𝔽 hms𝔽 μ𝔽 s j.val.2.2 hk u hu hnorm
  change MemLp u 2 ((μ𝔽).withDensity fun g ↦
    ENNReal.ofReal (((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹)) at h
  simpa only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero,
    max_self, one_mul, u] using h

-- For a family of admitted jets u, these are the two analytic inputs to
-- the Hilbert-space argument. Interpolants are lifted to the ambient space.
local notation "JetKernel(" a ", " hI ", " hs ", " u ")" =>
  (∀ f, f ∈ Θ(a, hI, hs) ↔ ∀ j, spectralSobolevPairing (F := F) f (u j) = 0)
local notation "JetInterpolation(" J ", " a ", " hI ", " hs ", " u ")" =>
  (∃ v : J → W(_, _, _), (∀ i, spectralSobolevPairing (F := F) (v i) (u i) = 1) ∧
    (∀ i j, i ≠ j → spectralSobolevPairing (F := F) (v i) (u j) = 0) ∧
    Dense (Submodule.span ℂ (range (fun i ↦ (Θ(a, hI, hs)).mkQ (v i))) :
      Set (spectralSobolevQuotient F a hI hs)))

/-- A total family of continuous functionals on a Hilbert space has norm-dense span. -/
private theorem spectralSobolevQuotient_basis_of_interpolation_dense_dual
    {Q J : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (Λ : J → StrongDual ℂ Q)
    (h : ∀ q : Q, (∀ j, Λ j q = 0) → q = 0) :
    Dense (Submodule.span ℂ (Set.range Λ) : Set (StrongDual ℂ Q)) := by
  let R := InnerProductSpace.toDual ℂ Q
  let v : J → Q := fun j ↦ R.symm (Λ j)
  have hv : Dense (Submodule.span ℂ (Set.range v) : Set Q) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro q hq
    apply h q
    intro j
    have hz := (Submodule.mem_orthogonal (Submodule.span ℂ (Set.range v)) q).mp hq
      (v j) (Submodule.subset_span (Set.mem_range_self j))
    simpa only [v, R, InnerProductSpace.toDual_symm_apply] using hz
  apply (R.surjective.denseRange.dense_image R.continuous hv).mono
  apply (Submodule.image_span_subset R.toLinearEquiv.toLinearMap
    (Set.range v) (Submodule.span ℂ (Set.range Λ))).mpr
  rintro _ ⟨j, rfl⟩
  change R (R.symm (Λ j)) ∈ Submodule.span ℂ (Set.range Λ)
  rw [R.apply_symm_apply]
  exact Submodule.subset_span (Set.mem_range_self j)

/-- Dense interpolants and a total lifted dual family form a spectral Markushevich basis. -/
private theorem spectralSobolevQuotient_basis_of_interpolation_construct
    {J E Q U : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (q : E → Q) (hq : Function.Surjective q)
    (D : StrongDual ℂ Q → U) (b : E → U → ℂ) (u : J → U)
    (hpair : ∀ (Λ : StrongDual ℂ Q) (f : E), Λ (q f) = b f (D Λ))
    (hu : ∀ j, ∃ Λ : StrongDual ℂ Q, D Λ = u j)
    (hzero : ∀ f : E, (∀ j, b f (u j) = 0) → q f = 0)
    (hV : ∃ v : J → E,
      (∀ i, b (v i) (u i) = 1) ∧
      (∀ i j, i ≠ j → b (v i) (u j) = 0) ∧
      Dense (Submodule.span ℂ (Set.range (fun i ↦ q (v i))) : Set Q)) :
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = u j := by
  classical
  choose Λ hΛ using hu
  obtain ⟨v, hvself, hvcross, hvdense⟩ := hV
  have he (j : J) (f : E) : Λ j (q f) = b f (u j) :=
    (hpair (Λ j) f).trans (congrArg (b f) (hΛ j))
  refine ⟨fun j ↦ q (v j), Λ, ?_, hΛ⟩
  refine ⟨fun i ↦ (he i (v i)).trans (hvself i),
    fun i j hij ↦ (he j (v i)).trans (hvcross i j hij), hvdense, ?_⟩
  apply spectralSobolevQuotient_basis_of_interpolation_dense_dual Λ
  intro z hz
  obtain ⟨f, rfl⟩ := hq z
  apply hzero f
  intro j
  exact (he j f).symm.trans (hz j)

/-- Paper: Theorems 10.2.1.1 and 10.2.2.1, pp. 440, 446. A common kernel
identifies the closed dual span in the Hilbert quotient. A dense family of
interpolants then supplies the other half of the Markushevich basis. -/
theorem spectralSobolevQuotient_basis_of_interpolation {J : Type*}
    (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) (u : J → W'(l, r, s))
    (_hK : JetKernel(a, hI, hs, u)) (_hV : JetInterpolation(J, a, hI, hs, u)) :
    let Q := spectralSobolevQuotient F a hI hs
    let D := spectralSobolevDualEmbedding F a hI hs
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = u j := by
  classical
  let N := globalThetaSobolev F a hI hs
  let D := spectralSobolevDualEmbedding F a hI hs
  have hpair (Λ : StrongDual ℂ (spectralSobolevQuotient F a hI hs))
      (f : W(l, r, s)) :
      Λ (N.mkQ f) = spectralSobolevPairing f (D Λ) := by
    exact (spectralSobolevPairing_dual hI hs (Λ.comp N.mkQL) f).2
  have hu (j : J) :
      ∃ Λ : StrongDual ℂ (spectralSobolevQuotient F a hI hs), D Λ = u j := by
    have hj : u j ∈ Set.range (spectralSobolevDualEmbedding F a hI hs) := by
      rw [(spectralSobolevDualEmbedding_isometry_range (F := F) a hI hs).2]
      exact fun f hf ↦ (_hK f).mp hf j
    exact hj
  refine spectralSobolevQuotient_basis_of_interpolation_construct
    (Q := spectralSobolevQuotient F a hI hs)
    N.mkQ N.mkQ_surjective D (spectralSobolevPairing (F := F)) u hpair hu ?_ _hV
  intro f hf
  exact (spectralSobolevQuotient_eq_zero a hI hs f).mpr ((_hK f).mpr hf)

local notation "lineHs(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "lineU(" χ ", " hs ")" =>
  (fun j ↦ (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j)))

/-- Paper: Theorem 10.2.1.1, p. 440. The norm-one dual and the discrete
zero sets in its charts give countably many admitted line jets. -/
theorem spectralLineJet_countable (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a s : ℝ) :
    Countable (SpectralLineJetIndex χ a s) := by
  have hK : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let Z (ω : PontryaginDual C₁) := {z : ℂ | 0 < multiplicity(χ ω, z)}
  have hc (ω : PontryaginDual C₁) : (Z ω).Countable := by
    have hm := (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn
    have hcod : (Z ω)ᶜ ∈ Filter.codiscrete ℂ := by
      filter_upwards [hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
      rcases hz.2 with h | h <;> simp [Z, h]
    let : DiscreteTopology (Z ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hcod).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let W := ⋃ ω, Z ω
  let : Countable W := (Set.countable_iUnion hc).to_subtype
  have hz (j : SpectralLineJetIndex χ a s) : shift(a, j.val.2.1) ∈ W := by
    apply Set.mem_iUnion.mpr
    refine ⟨j.val.1, ?_⟩
    exact Nat.zero_lt_of_lt (lt_of_lt_of_le j.property (min_le_left _ _))
  let e (j : SpectralLineJetIndex χ a s) : PontryaginDual C₁ × W × ℕ :=
    (j.val.1, ⟨shift(a, j.val.2.1), hz j⟩, j.val.2.2)
  apply Function.Injective.countable (f := e)
  intro i j hij
  have him := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.im) hij
  have hω := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.1) hij
  have hk := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.2) hij
  exact Subtype.ext (Prod.ext hω (Prod.ext (by simpa [e] using him) hk))

section TestDuality

local notation "E" => ModulatedExponentialDecay m𝔽 univ
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω
local notation "ℬ₀" => ↥(adelePolarSubspace F)

/-- A jointly continuous family on a compact parameter space preserves sequence
convergence uniformly in the parameter. -/
private theorem existsUnique_spectralLineTestCompletion_uniform
    {H Z : Type*} [TopologicalSpace H] [CompactSpace H] [UniformSpace Z]
    (T : H → Z → Z) (hT : Continuous (fun p : H × Z ↦ T p.1 p.2))
    (u : ℕ → Z) (v : Z) (hu : Tendsto u atTop (𝓝 v)) :
    TendstoUniformly (fun n k ↦ T k (u n)) (fun k ↦ T k v) atTop := by
  intro U hU
  have hc : Continuous (fun p : Z × H ↦ T p.2 p.1) := hT.comp continuous_swap
  obtain ⟨V, hV, h⟩ := (isCompact_univ (X := H)).mem_uniformity_of_prod
    (f := fun f : Z ↦ fun k : H ↦ T k f)
    (s := univ) (q := v) hc.continuousOn (mem_univ v) (symm_le_uniformity hU)
  rw [nhdsWithin_univ] at hV
  filter_upwards [hu.eventually hV] with n hn k
  exact h (u n) hn k (mem_univ k)

/-- Compact character averaging preserves density of an equivariant map. -/
private theorem existsUnique_spectralLineTestCompletion_dense
    {H X Y : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H] [CompactSpace H]
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [T2Space X] [PolynormableSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (μ : Measure H) [μ.IsHaarMeasure]
    (σ : H →* (X →L[ℂ] X)) (τ : H →* (Y →L[ℂ] Y))
    (hσ : Continuous (fun p : H × X ↦ σ p.1 p.2))
    (hτ : Continuous (fun p : H × Y ↦ τ p.1 p.2))
    (hborn : ∀ p : Seminorm ℂ X,
      (∀ B : Set X, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (ω : PontryaginDual H) (j : X →L[ℂ] Y) (hd : DenseRange j)
    (heq : ∀ k f, j (σ k f) = τ k (j f))
    (i : actionIsotype σ ω →L[ℂ] actionIsotype τ ω)
    (hi : ∀ f, (i f : Y) = j (f : X)) : DenseRange i := by
  letI : Module ℝ X := Module.restrictScalars ℝ ℂ X
  letI : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X
  letI : LocallyConvexSpace ℝ X :=
    (PolynormableSpace.withSeminorms ℂ X).toLocallyConvexSpace
  letI : NormedSpace ℝ Y := NormedSpace.complexToReal
  have hbornY (p : Seminorm ℂ Y)
      (hp : ∀ B : Set Y, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) :
      Continuous p := by
    obtain ⟨M, hM⟩ := hp _ (NormedSpace.isVonNBounded_closedBall ℂ Y 1)
    have hball : p.closedBall 0 (max M 0 + 1) ∈ 𝓝 (0 : Y) := by
      refine Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : Y) zero_lt_one) ?_
      intro x hx
      rw [Seminorm.mem_closedBall_zero]
      exact (hM ⟨x, hx, rfl⟩).trans
        (le_of_lt <| lt_of_le_of_lt (le_max_left M 0) (lt_add_one _))
    exact p.continuous' hball
  obtain ⟨A, hA⟩ := (existsUnique_compactActionIsotypicAverage μ σ hσ
    hborn (existsUnique_spectralLineTestCompletion_uniform (Z := X)
      (fun k f ↦ σ k f) hσ) ω).exists
  obtain ⟨B, hB⟩ := (existsUnique_compactActionIsotypicAverage μ τ hτ
    hbornY (existsUnique_spectralLineTestCompletion_uniform (Z := Y)
      (fun k f ↦ τ k f) hτ) ω).exists
  have hrangeA := compactActionAverage_range μ σ hσ ω A hA
  have hrangeB := compactActionAverage_range μ τ hτ ω B hB
  let A' := A.codRestrict (actionIsotype σ ω) (by
    intro u
    rw [← hrangeA]
    exact ⟨u, rfl⟩)
  let B' := B.codRestrict (actionIsotype τ ω) (by
    intro u
    rw [← hrangeB]
    exact ⟨u, rfl⟩)
  have hsurj : Surjective B' := by
    intro u
    have hu : (u : Y) ∈ B.toLinearMap.range := hrangeB.symm ▸ u.property
    obtain ⟨v, hv⟩ := hu
    exact ⟨v, Subtype.ext hv⟩
  have hcomm (f : X) : j (A f) = B (j f) := by
    letI : SeparatingDual ℂ Y := locallyConvexSpace_separatingDual ℂ Y
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro φ
    obtain ⟨_, hs⟩ := hA f
    obtain ⟨_, ht⟩ := hB (j f)
    have hs' := LinearMap.congr_fun hs (φ.comp j)
    have ht' := LinearMap.congr_fun ht φ
    change φ (j (A f)) =
      ∫ k : H, φ (j (star (ω k : ℂ) • σ k f)) ∂μ.restrict univ at hs'
    change φ (B (j f)) =
      ∫ k : H, φ (star (ω k : ℂ) • τ k (j f)) ∂μ.restrict univ at ht'
    simpa only [map_smul j, heq, ← ht'] using hs'
  have hcomp : (i : _ → _) ∘ A' = (B' : _ → _) ∘ j :=
    funext fun f ↦ Subtype.ext ((hi (A' f)).trans (hcomm f))
  apply DenseRange.of_comp (g := A')
  rw [hcomp]
  exact hsurj.denseRange.comp hd B'.continuous

/-- Paper: (10.2.1.7), p. 441. The weighted completion map on exponential-decay
tests preserves the norm-one isotype and has dense image in its Sobolev isotype.
Its transpose evaluates by pairing with the weighted test.
Deviation: The transpose uses the conjugate isotype in the negative space.
The norm weight is applied to the full test space in the diagram. Appendix D's
two-sided decay topology uses growing exponential weights in log coordinates.
The decaying factors on p. 441 would all be bounded by the zeroth weight. -/
theorem existsUnique_spectralLineTestCompletion (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    ∃! i : Eω(ω) →L[ℂ] Wω(le_rfl (a := (0 : ℝ)), hs, ω),
      (∀ φ, ((i φ).val : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a φ.val.val) ∧
        DenseRange i ∧
        ∃ T : W'(0, 0, s) →L[ℂ] StrongDual ℂ Eω(ω),
          (∀ u φ, T u φ = spectralSobolevPairing (F := F) (i φ).val u) ∧
          ∀ u, (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽]
            fun g ↦ (ω⁻¹ k : ℂ) * u g) → T u = 0 → u = 0 := by
  have hshift : (fun b : ℝ ↦ b - a) '' univ = univ :=
    image_univ_of_surjective fun b ↦ ⟨b + a, add_sub_cancel_right b a⟩
  have hShiftEx : ∃ S : E ≃L[ℂ] E,
      ∀ f, (S f).val = modulationWeight m𝔽 a f.val :=
    (congrArg (fun J : Set ℝ ↦ ∃ S : E ≃L[ℂ] ModulatedExponentialDecay m𝔽 J,
      ∀ f, (S f).val = modulationWeight m𝔽 a f.val) hshift).mp
      (modulatedExponentialDecay_shift_equiv (G := C𝔽) m𝔽 univ hm𝔽 hms𝔽
        ordConnected_univ univ_nonempty a)
  let S := hShiftEx.choose
  have hS := hShiftEx.choose_spec
  have hDenseEx :=
    modulatedIntervalSobolev_dense (G := C𝔽) m𝔽 hm𝔽 0 0 s le_rfl hs univ
      isOpen_univ ordConnected_univ (subset_univ _)
  let j₀ := hDenseEx.choose
  have hj₀inj := hDenseEx.choose_spec.1
  have hj₀dense := hDenseEx.choose_spec.2.1
  have hj₀coe := hDenseEx.choose_spec.2.2
  have hEquivEx := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 0 0 s
  let e := hEquivEx.choose
  have he := hEquivEx.choose_spec
  let j : E →L[ℂ] W(0, 0, s) :=
    e.symm.toContinuousLinearMap.comp (j₀.comp S.toContinuousLinearMap)
  have hjinj : Injective j := e.symm.injective.comp (hj₀inj.comp S.injective)
  have hjdense : DenseRange j := e.symm.surjective.denseRange.comp
    (hj₀dense.comp S.surjective.denseRange j₀.continuous) e.symm.continuous
  have hj (f : E) : (j f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a f.val := by
    have h₀ : (j₀ (S f) : C𝔽 → ℂ) =ᵐ[μ𝔽] (S f).val := by
      rw [ideleClassTamagawaMeasure_eq_smul_canonical (F := F)]
      exact Measure.ae_smul_measure (hj₀coe (S f)) _
    have he' := (he (j f)).1
    have hej : e (j f) = j₀ (S f) := by simp [j]
    rw [hej] at he'
    exact he'.symm.trans (h₀.trans (ae_of_all _ fun g ↦ congrFun (hS f) g))
  let σ : C₁ →* (E →L[ℂ] E) := (ρE).comp (ideleClassNorm F).ker.subtype
  let τ : C₁ →* (W(0, 0, s) →L[ℂ] W(0, 0, s)) := ρ(0, 0, s, le_rfl, hs)
  have hE := (exists_modulatedExponentialDecay_translationAction (G := C𝔽) m𝔽 univ
    hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose_spec
  have hjρ (k : C₁) (f : E) : j (σ k f) = τ k (j f) := by
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs k.val (j f)
    have ht := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (hj f)
    filter_upwards [hj (σ k f), htr, ht] with g hleft hright hcomp
    change (j f) (k.val⁻¹ * g) = (modulationWeight m𝔽 a f.val) (k.val⁻¹ * g) at hcomp
    have hweight : (modulationWeight m𝔽 a (σ k f).val) g =
        (modulationWeight m𝔽 a f.val) (k.val⁻¹ * g) := by
      have hk : m𝔽 k.val = 1 := k.property
      have hn : m𝔽 (k.val⁻¹ * g) = m𝔽 g := by
        rw [map_mul, map_inv, hk, inv_one, one_mul]
      change Complex.ofReal (((m𝔽 g).val : ℝ) ^ a) * ((ρE) k.val f).val g =
        Complex.ofReal (((m𝔽 (k.val⁻¹ * g)).val : ℝ) ^ a) * f.val (k.val⁻¹ * g)
      have hv := congrArg (fun z : ℂ ↦ Complex.ofReal (((m𝔽 g).val : ℝ) ^ a) * z)
        (hE.1 k.val f g)
      have hw := congrArg (fun t : ℝ≥0ˣ ↦
        Complex.ofReal ((t.val : ℝ) ^ a) * f.val (k.val⁻¹ * g)) hn.symm
      exact hv.trans hw
    exact hleft.trans (hweight.trans (hcomp.symm.trans hright.symm))
  let i : actionIsotype σ ω →L[ℂ] actionIsotype τ ω :=
    (j.comp (actionIsotype σ ω).subtypeL).codRestrict (actionIsotype τ ω) (by
      intro φ
      apply (mem_actionIsotype τ ω _).2
      intro k
      change τ k (j φ.val) = (ω k : ℂ) • j φ.val
      rw [← hjρ, ((mem_actionIsotype σ ω _).1 φ.property k), map_smul])
  have hicoe (φ : Eω(ω)) : ((i φ).val : C𝔽 → ℂ) =ᵐ[μ𝔽]
      modulationWeight m𝔽 a φ.val.val := hj φ.val
  letI : T2Space E := T2Space.of_injective_continuous (f := j) hjinj j.continuous
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let sectionNorm : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hsection : Function.RightInverse sectionNorm m𝔽 := canonicalIdeleNormSection_rightInverse F
  letI : CompleteSpace E := modulatedExponentialDecay_complete (G := C𝔽) m𝔽 univ hm𝔽
    ordConnected_univ univ_nonempty sectionNorm hsection
  letI : CompactSpace C₁ :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker (m := m𝔽) hm𝔽)
  letI : MeasurableSpace C₁ := borel _
  letI : BorelSpace C₁ := ⟨rfl⟩
  have hσ : Continuous (fun p : C₁ × E ↦ σ p.1 p.2) :=
    hE.2.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hτ : Continuous (fun p : C₁ × W(0, 0, s) ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hidense : DenseRange i := existsUnique_spectralLineTestCompletion_dense
    (H := C₁) (X := E) (Y := W(0, 0, s)) Measure.haar σ τ hσ hτ
    (modulatedExponentialDecay_bornological (G := C𝔽) m𝔽 univ hm𝔽 ordConnected_univ
      univ_nonempty sectionNorm hsection) ω j hjdense hjρ i (fun _ ↦ rfl)
  let D : StrongDual ℂ W(0, 0, s) ≃ₗᵢ[ℂ] W'(0, 0, s) :=
    (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs).exists.choose
  let T' : W'(0, 0, s) →L[ℂ] StrongDual ℂ Eω(ω) :=
    (((actionIsotype τ ω).subtypeL.comp i).precomp ℂ).comp
      D.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hT (u : W'(0, 0, s)) (φ : Eω(ω)) :
      T' u φ = spectralSobolevPairing (F := F) (i φ).val u := by
    change (D.symm u) (i φ).val = _
    have h := (spectralSobolevPairing_dual le_rfl hs (D.symm u) (i φ).val).2
    change (D.symm u) (i φ).val = spectralSobolevPairing (F := F) (i φ).val
      (D (D.symm u)) at h
    exact h.trans (congrArg (spectralSobolevPairing (F := F) (i φ).val) (D.apply_symm_apply u))
  refine ⟨i, ⟨hicoe, hidense, T', hT, ?_⟩, ?_⟩
  · intro u hu hTu
    let Λ : StrongDual ℂ (actionIsotype τ ω) := (D.symm u).comp (actionIsotype τ ω).subtypeL
    have hΛ : Λ = 0 := by
      apply DFunLike.coe_injective
      apply hidense.equalizer Λ.continuous (0 : StrongDual ℂ (actionIsotype τ ω)).continuous
      funext φ
      change T' u φ = 0
      exact congrArg (fun L : StrongDual ℂ Eω(ω) ↦ L φ) hTu
    by_contra hu0
    obtain ⟨f, hf⟩ := (spectralSobolevPairing_isotype le_rfl hs ω).2 u hu hu0
    apply hf
    have h := (spectralSobolevPairing_dual le_rfl hs (D.symm u) f.val).2
    change (D.symm u) f.val = spectralSobolevPairing (F := F) f.val
      (D (D.symm u)) at h
    exact (h.trans (congrArg (spectralSobolevPairing (F := F) f.val)
      (D.apply_symm_apply u))).symm.trans
        (congrArg (fun L : StrongDual ℂ (actionIsotype τ ω) ↦ L f) hΛ)
  · intro i' hi'
    apply ContinuousLinearMap.ext
    intro φ
    apply Subtype.ext
    exact Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq
      ((hi'.1 φ).trans (hicoe φ).symm))

/-- Paper: (10.2.1.8), pp. 441–442. Pullback sends a functional on the
isotypic Sobolev quotient injectively into the test dual and annihilates
the polar-free theta tests of that isotype.
Deviation: Pull back along the norm-weighted completion map of (10.2.1.7). -/
theorem spectralLineIsotypeDual_pullback (a : ℝ) {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let N := (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype
    let i := (existsUnique_spectralLineTestCompletion a hs ω).exists.choose
    let D : StrongDual ℂ (spectralSobolevIsotypeQuotient F a hI hs ω) →L[ℂ]
        StrongDual ℂ Eω(ω) := (N.mkQL.comp i).precomp ℂ
    Injective D ∧ ∀ Λ (φ : Eω(ω)) (f : ℬ₀), φ.val.val = homogeneousAdelicTheta ω f.val → D Λ φ = 0 := by
  intro hI N i D
  have hi := (existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose_spec
  constructor
  · have hd : DenseRange (N.mkQL.comp i) :=
      N.mkQ_surjective.denseRange.comp hi.2.1 N.mkQL.continuous
    intro Λ₁ Λ₂ hΛ
    apply DFunLike.coe_injective
    exact hd.equalizer Λ₁.continuous Λ₂.continuous
      (funext fun φ ↦ congrArg (fun T : StrongDual ℂ Eω(ω) ↦ T φ) hΛ)
  · intro Λ φ f hφ
    let x : globalPolarFreeThetaSubmodule (F := F) ω :=
      ⟨Submodule.Quotient.mk f.val, Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩
    let j := (exists_globalHomogeneousThetaSobolevInclusion
      (F := F) (a := a) hI hs ω).choose
    have hj := (exists_globalHomogeneousThetaSobolevInclusion
      (F := F) (a := a) hI hs ω).choose_spec.2.2
    have he : (i φ).val = (j x).val.val := by
      apply Lp.ext
      apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
      have hw : modulationWeight m𝔽 a φ.val.val =ᵐ[μ𝔽]
          modulationWeight m𝔽 a (homogeneousAdelicTheta ω f.val) :=
        Filter.Eventually.of_forall (congrFun (congrArg (modulationWeight m𝔽 a) hφ))
      exact (hi.1 φ).trans (hw.trans (hj f x rfl).2.symm)
    have hn : i φ ∈ N := by
      change (i φ).val ∈ Θ(a, hI, hs)
      rw [he]
      exact (j x).val.property
    change Λ (N.mkQ (i φ)) = 0
    exact (congrArg Λ ((Submodule.Quotient.mk_eq_zero N).mpr hn)).trans (map_zero Λ)

end TestDuality

/-- Every logarithmic moment of a function integrable against all quasi-characters is
integrable against every real norm twist. -/
private theorem spectralLineJet_functional_moment
    {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (χ : QuasiCharacter G) (u : G → ℂ)
    (hu : ∀ c : QuasiCharacter G, Integrable (fun g ↦ u g * c g) μ) (σ : ℝ) (n : ℕ) :
    Integrable (fun g ↦ u g * (Real.log ((m g).val : ℝ) : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := by
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  let tw (w : ℝ) := quasiCharacterNormTwist m.toMonoidHom m.continuous χ (w : ℂ)
  have h1 := (hu (tw (σ + 1))).norm
  have h2 := (hu (tw (σ - 1))).norm
  have hmeas : AEStronglyMeasurable (fun g ↦ u g * (Real.log ((m g).val : ℝ) : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := by
    have hL : AEStronglyMeasurable (fun g ↦ (Real.log ((m g).val : ℝ) : ℂ) ^ n) μ :=
      ((Complex.measurable_ofReal.comp hlog).pow_const n).aestronglyMeasurable
    refine ((hu (tw σ)).aestronglyMeasurable.mul hL).congr (ae_of_all _ fun g ↦ ?_)
    simp only [Pi.mul_apply, tw]
    ring
  refine ((h1.add h2).const_mul (n.factorial : ℝ)).mono' hmeas (ae_of_all _ fun g ↦ ?_)
  set L := Real.log ((m g).val : ℝ) with hLdef
  have hnorm (w : ℝ) : ‖quasiCharacterNormTwist m.toMonoidHom m.continuous χ (w : ℂ) g‖ =
      ‖χ g‖ * Real.exp (w * L) := by
    rw [quasiCharacterNormTwist_eq_exp, norm_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal]
  have hpow : |L| ^ n ≤ n.factorial * (Real.exp L + Real.exp (-L)) := by
    have h := Real.pow_div_factorial_le_exp |L| (abs_nonneg L) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have habs : Real.exp |L| ≤ Real.exp L + Real.exp (-L) := by
      rcases abs_cases L with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] <;>
        linarith [Real.exp_pos L, Real.exp_pos (-L)]
    rw [div_le_iff₀ hf] at h
    nlinarith
  change ‖u g * (L : ℂ) ^ n * tw σ g‖ ≤
    (n.factorial : ℝ) * (‖u g * tw (σ + 1) g‖ + ‖u g * tw (σ - 1) g‖)
  simp only [tw, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hnorm]
  have hA : 0 ≤ ‖u g‖ * (‖χ g‖ * Real.exp (σ * L)) := by positivity
  have e1 : Real.exp ((σ + 1) * L) = Real.exp (σ * L) * Real.exp L := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((σ - 1) * L) = Real.exp (σ * L) * Real.exp (-L) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2]
  calc ‖u g‖ * |L| ^ n * (‖χ g‖ * Real.exp (σ * L))
      = (‖u g‖ * (‖χ g‖ * Real.exp (σ * L))) * |L| ^ n := by ring
    _ ≤ (‖u g‖ * (‖χ g‖ * Real.exp (σ * L))) * (n.factorial * (Real.exp L + Real.exp (-L))) :=
        mul_le_mul_of_nonneg_left hpow hA
    _ = _ := by ring

/-- The pairing of a weighted function with a line jet is the derivative of its
norm-twisted Mellin integral at the shifted point. -/
private theorem spectralLineJet_functional_deriv
    {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (χ : QuasiCharacter G) (u : G → ℂ)
    (hu : ∀ c : QuasiCharacter G, Integrable (fun g ↦ u g * c g) μ) (a t : ℝ) (k : ℕ) :
    ∫ g, modulationWeight m a u g *
        (quasiCharacterNormTwist m.toMonoidHom m.continuous χ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
          (Real.log ((m g).val : ℝ) : ℂ) ^ k) ∂μ =
      iteratedDeriv k (fun w ↦ ∫ g, u g *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ)
        ((a : ℂ) + (t : ℂ) * Complex.I) := by
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m μ χ
    (α := a - 1) (β := a + 1) (fun σ _ n ↦ spectralLineJet_functional_moment m μ χ u hu σ n) k
    (z := (a : ℂ) + (t : ℂ) * Complex.I) (by simp)
  rw [hderiv]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  have hpos : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (m g).ne_zero)
  change (((((m g).val : ℝ) ^ a : ℝ)) : ℂ) * u g * _ = _
  dsimp only
  rw [quasiCharacterNormTwist_eq_exp, quasiCharacterNormTwist_eq_exp,
    Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Complex.ofReal_mul]
  have e : Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((m g).val : ℝ) : ℂ)) =
      Complex.exp ((Real.log ((m g).val : ℝ) : ℂ) * (a : ℂ)) *
        Complex.exp ((((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((m g).val : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  ring


/-- Every function in the two-sided decay space is integrable against every quasi-character. -/
private theorem spectralLineJet_functional_integrable
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (φ : ModulatedExponentialDecay m univ)
    (c : QuasiCharacter G) : Integrable (fun g ↦ φ.val g * c g) μ :=
  modulatedFourierMellin_integrable m univ hm ordConnected_univ univ_nonempty μ isOpen_univ hms φ
    ⟨c, mem_univ _⟩

/-- Paper: (10.2.1.9), p. 442. A surviving line jet acts on the Sobolev
space by the integral of the input against that jet. On a weighted exponential-
decay test this is precisely the derivative in the existing Mellin chart. -/
theorem spectralLineJet_functional (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a s : ℝ} (hs : 1 < s) (j : SpectralLineJetIndex χ a s) :
    ∃ Λ : StrongDual ℂ W(0, 0, s),
      (∀ f : W(0, 0, s), Integrable (fun g ↦ f g * lineJet(χ, j) g) μ𝔽 ∧
        Λ f = ∫ g, f g * lineJet(χ, j) g ∂μ𝔽) ∧
      ∀ (φ : ModulatedExponentialDecay m𝔽 univ) (f : W(0, 0, s)),
        (f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a φ.val →
        Λ f = iteratedDeriv j.val.2.2 (fun z ↦ modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
          φ.val (ideleClassNormTwist (χ j.val.1) z)) (shift(a, j.val.2.1)) := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  let Td := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs0).exists.choose
  let u : W'(0, 0, s) := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
  have hac : μ𝔽 ≪ L2μ'(0, 0, s) := by
    refine withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun g ↦ ?_)
    · exact ((continuous_intervalSobolevDensity' 0 0 s).measurable.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp
          (isProperMap_ideleClassNorm F).continuous)).measurable.log).inv.ennreal_ofReal.aemeasurable
    · exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (intervalSobolevDensity_pos 0 0 s _))
  have hae : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] lineJet(χ, j) := hac.ae_le (MemLp.coeFn_toLp _)
  have hpair (f : W(0, 0, s)) : Integrable (fun g ↦ f g * lineJet(χ, j) g) μ𝔽 ∧
      Td.symm u f = ∫ g, f g * lineJet(χ, j) g ∂μ𝔽 := by
    have h := spectralSobolevPairing_dual le_rfl hs0 (Td.symm u) f
    have hTu : Td (Td.symm u) = u := Td.apply_symm_apply u
    have hc : (fun g ↦ f g * Td (Td.symm u) g) =ᵐ[μ𝔽] fun g ↦ f g * lineJet(χ, j) g := by
      rw [hTu]
      exact hae.mono fun g hg ↦ congrArg (f g * ·) hg
    exact ⟨h.1.congr hc, h.2.trans (integral_congr_ae hc)⟩
  refine ⟨Td.symm u, hpair, fun φ f hf ↦ ?_⟩
  let χq : QuasiCharacter C𝔽 :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ j.val.1)
  have hc : (fun g ↦ f g * lineJet(χ, j) g) =ᵐ[μ𝔽]
      fun g ↦ modulationWeight m𝔽 a φ.val g *
        (quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(0, j.val.2.1)) g *
          (Real.log ((m𝔽 g).val : ℝ) : ℂ) ^ j.val.2.2) :=
    hf.mono fun g hg ↦ by dsimp only; rw [hg]; rfl
  have key := spectralLineJet_functional_deriv m𝔽 μ𝔽 χq φ.val
    (spectralLineJet_functional_integrable m𝔽 hm𝔽 hms𝔽 μ𝔽 φ) a j.val.2.1 j.val.2.2
  have hF : (fun z ↦ modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val
      (ideleClassNormTwist (χ j.val.1) z)) = fun w ↦ ∫ g, φ.val g *
        quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq w g ∂μ𝔽 :=
    funext fun z ↦ modulatedFourierMellin_univ m𝔽 hm𝔽 μ𝔽 _ _
  rw [(hpair f).2, integral_congr_ae hc, hF]
  exact key

section

universe u v

/-- Integrating scalar multiples of a commutative action preserves every eigenspace. -/
private theorem spectral_integrated_action_eigenvector
    {G : Type u} [CommGroup G] [MeasurableSpace G] (μ : Measure G)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ρ : G →* (V →L[ℂ] V)) (f : G → ℂ) (u v : V)
    (hv : HasPettisIntegral (.positive μ) (fun g ↦ f g • ρ g u) v)
    (k : G) (c : ℂ) (hu : ρ k u = c • u) : ρ k v = c • v := by
  have hev (δ : StrongDual ℂ V) : δ v = ∫ g, δ (f g • ρ g u) ∂μ :=
    congrArg (fun z : PettisWeakCompletion V ↦
      (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) hv.2
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro δ
  have he (g : G) : ρ k (f g • ρ g u) = c • (f g • ρ g u) := by
    rw [map_smul]
    have hc : ρ k (ρ g u) = ρ g (ρ k u) := by
      change (ρ k * ρ g) u = (ρ g * ρ k) u
      rw [← map_mul, ← map_mul, mul_comm k g]
    rw [hc, hu, map_smul, smul_comm]
  calc
    δ (ρ k v) = ∫ g, δ (ρ k (f g • ρ g u)) ∂μ :=
      hev (δ.comp (ρ k))
    _ = ∫ g, c • δ (f g • ρ g u) ∂μ :=
      integral_congr_ae (.of_forall fun g ↦ (congrArg δ (he g)).trans (map_smul δ c _))
    _ = c • δ v := by rw [integral_smul, ← hev δ]
    _ = δ (c • v) := (map_smul δ c v).symm

end

/-- Paper: (10.2.1.10), pp. 442–443. The band-limited approximate unit acts
by convolution on the fixed norm-one isotype and converges there strongly.
Deviation: The Fourier band is centered on the inverse lift for the
left-translation convention of §9.3. -/
theorem exists_spectralLineIsotypeConvolution (χ : PontryaginDual C𝔽) {s : ℝ} (hs : 0 ≤ s) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let E := Wω(hI, hs, χ.comp restriction)
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    ∃ (φ : ℕ → SchwartzBruhat C𝔽) (P : ℕ → (E →L[ℂ] E)),
      (∀ n, ‖A (φ n)‖ ≤ 2) ∧
      (∀ n (k : C₁) g, (φ n) (k.val⁻¹ * g) = (χ k.val : ℂ) * (φ n) g) ∧
      (∀ n, tsupport (lcaFourier μ𝔽 (φ n)) ⊆
        modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n) ∧
      (∀ n (f : E), (P n f).val = A (φ n) f.val) ∧
      ∀ f : E, Tendsto (fun n ↦ P n f) atTop (𝓝 f) := by
  intro hI E A
  let τ := hardySobolevTranslation μ𝔽 m𝔽 0 0 s hI hs
  let B := (existsUnique_singletonDecay_lineAction μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs).exists.choose
  have hB := (existsUnique_singletonDecay_lineAction μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs).exists.choose_spec.1
  have hA := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec
  let e := (modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms𝔽 0).choose
  have he (f : ModulatedExponentialDecay m𝔽 {0}) : (e f : C𝔽 → ℂ) = f.val := by
    exact ((modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms𝔽 0).choose_spec f).trans
      (modulationWeight_zero m𝔽 f.val)
  have hAB (f : ModulatedExponentialDecay m𝔽 {0}) : A (e f) = B f := by
    apply ContinuousLinearMap.ext
    intro u
    have hp : (fun g ↦ (e f).val g • τ g u) = (fun g ↦ f.val g • τ g u) :=
      funext fun g ↦ congrArg (fun z : ℂ ↦ z • τ g u) (congrFun (he f) g)
    have hP : HasPettisIntegral (.positive μ𝔽) (fun g ↦ f.val g • τ g u) (A (e f) u) :=
      hp ▸ hA (e f) u
    exact hP.unique (hB f u)
  let φ := (exists_singletonDecay_isotype_approximation μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs χ⁻¹).choose
  have hφ := (exists_singletonDecay_isotype_approximation μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs χ⁻¹).choose_spec
  have hmem (n : ℕ) (u : E) : A (e (φ n)) u.val ∈ E := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    exact spectral_integrated_action_eigenvector μ𝔽 τ (e (φ n)).val u.val
      (A (e (φ n)) u.val) (hA (e (φ n)) u.val) k.val (χ k.val : ℂ)
      ((mem_actionIsotype _ _ _).mp u.property k)
  let P (n : ℕ) : E →L[ℂ] E :=
    ((A (e (φ n))).comp E.subtypeL).codRestrict E (hmem n)
  refine ⟨fun n ↦ e (φ n), P, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hAB]
    exact hφ.1 n
  · intro n k g
    have hchar : star ((χ⁻¹) k.val : ℂ) = (χ k.val : ℂ) := by
      change star (((χ k.val)⁻¹ : Circle) : ℂ) = _
      rw [Circle.coe_inv_eq_conj]
      exact star_star _
    calc
      e (φ n) (k.val⁻¹ * g) = (φ n).val (k.val⁻¹ * g) := congrFun (he (φ n)) _
      _ = star ((χ⁻¹) k.val : ℂ) * (φ n).val g := hφ.2.1 n k g
      _ = (χ k.val : ℂ) * e (φ n) g := congrArg₂ (· * ·) hchar (congrFun (he (φ n)) g).symm
  · intro n
    simpa only [he, modulationWeight_zero] using hφ.2.2.1 n
  · intro n f
    rfl
  · intro f
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n ↦ A (e (φ n)) f.val) atTop (𝓝 f.val)
    have h : Tendsto (fun n ↦ B (φ n) f.val) atTop (𝓝 f.val) :=
      hφ.2.2.2 ⟨f.val, by simpa only [inv_inv] using f.property⟩
    exact h.congr' (Filter.Eventually.of_forall fun n ↦
      congrArg (fun T : W(0, 0, s) →L[ℂ] W(0, 0, s) ↦ T f.val) (hAB (φ n)).symm)

private theorem spectralJet_lp_norm_sq {μ : Measure C𝔽} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂μ := by
  have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hre, L2.inner_def]
  have hre_int : (∫ g : C𝔽, inner ℂ (u g) (u g) ∂μ).re =
      ∫ g : C𝔽, (inner ℂ (u g) (u g)).re ∂μ :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
  rw [hre_int]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u g)

private theorem spectralZeroJet_continuous (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) :
    Continuous (spectralZeroJet χ b t k) :=
  (ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).continuous.mul
    ((Complex.continuous_ofReal.comp (continuous_logModule' m𝔽)).pow k)

private theorem spectralZeroJet_norm_sq (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖spectralZeroJet χ b t k g‖ ^ 2 = Real.exp (2 * b * logNorm g) * (logNorm g) ^ (2 * k) := by
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have htwist : ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g‖ =
      Real.exp (b * logNorm g) := by
    change ‖(χ g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
      mul_comm]
  change ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
    (logNorm g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hexp : Real.exp (b * logNorm g) ^ 2 = Real.exp (2 * b * logNorm g) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hpow : (|logNorm g| ^ k) ^ 2 = (logNorm g) ^ (2 * k) := by
    calc
      (|logNorm g| ^ k) ^ 2 = (|logNorm g| ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      _ = ((logNorm g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * k) := (pow_mul _ _ _).symm
  rw [hexp, hpow]

private theorem symmIntervalSobolevDensity_eq {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem symmIntervalSobolevDensity_pos {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    0 < intervalSobolevDensity (-α) α s x := by
  rw [symmIntervalSobolevDensity_eq hα]
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

private theorem symmIntervalSobolevDensity_inv_continuous {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity (-α) α s (logNorm g))⁻¹) := by
  have hρ : Continuous (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) := by
    have heq : (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) =
        fun g : C𝔽 ↦ Real.exp (2 * α * |logNorm g|) * (1 + (logNorm g) ^ 2) ^ (s / 2) :=
      funext fun g ↦ symmIntervalSobolevDensity_eq hα s (logNorm g)
    rw [heq]
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_logModule' m𝔽).abs)).mul
      (((continuous_const : Continuous (fun _ : C𝔽 ↦ (1 : ℝ))).add
        ((continuous_logModule' m𝔽).pow 2)).rpow_const fun g ↦ Or.inl (by
          change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
          positivity))
  exact hρ.inv₀ fun g ↦ (symmIntervalSobolevDensity_pos hα s (logNorm g)).ne'

private theorem pow_mul_rpow_inv_continuous (k : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  (continuous_id.pow (2 * k)).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem spectralLineJet_integral_pos {s : ℝ} (hs : 1 < s) {k : ℕ}
    (hkN : k < Nat.ceil ((s - 1) / 2)) :
    0 < ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽 := by
  have hk' : (k : ℝ) < (s - 1) / 2 := Nat.lt_ceil.mp hkN
  have hk : 2 * (k : ℝ) + 1 < s := by linarith
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let fk : ℝ → ℝ := fun x ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have hfk_int : Integrable fk volume := integrable_pow_mul_rpow_inv hk
  have hmp : MeasurePreserving (fun g : C𝔽 ↦ logNorm g) ν volume :=
    sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hlogm : AEMeasurable (fun g : C𝔽 ↦ logNorm g) ν :=
    (continuous_logModule' m𝔽).measurable.aemeasurable
  have hν_eq : ∫ g : C𝔽, fk (logNorm g) ∂ν = ∫ x : ℝ, fk x ∂volume := by
    rw [← hmp.map_eq,
      integral_map hlogm (pow_mul_rpow_inv_continuous k s).aestronglyMeasurable]
  have hvol_pos : 0 < ∫ x : ℝ, fk x ∂volume := by
    let c : ℝ := ((5 : ℝ) ^ (s / 2))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c) volume :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ≤ fk x := by
      intro x
      by_cases hx : x ∈ Icc (1 : ℝ) 2
      · rw [indicator_of_mem hx]
        have hpow : (1 : ℝ) ≤ x ^ (2 * k) := one_le_pow₀ hx.1
        have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith [hx.1, hx.2]
        have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
        have hinv : c ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
        calc
          c = 1 * c := (one_mul c).symm
          _ ≤ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
            mul_le_mul hpow hinv hc.le (by positivity)
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
          (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    have hint_le : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume ≤
        ∫ x : ℝ, fk x ∂volume :=
      integral_mono hind_int hfk_int hle
    have hind_val : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume = c := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      norm_num
    linarith
  have hμ_eq : (∫ g : C𝔽, fk (logNorm g) ∂μ𝔽) =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, fk x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  change 0 < ∫ g : C𝔽, fk (logNorm g) ∂μ𝔽
  rw [hμ_eq]
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  exact mul_pos hfac_pos hvol_pos

/-- Paper: Proposition 10.2.1.3 and (10.2.1.12), p. 443. A single annulus
contains all the a-line jet classes.
Deviation: Use the truncated multiplicity intended by the reference to
(10.2.1.6). The lower bound asserts disjointness from the open ball, which
also makes sense for an empty zero set. -/
theorem spectralLineJet_annulus (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralLineJetIndex χ a s,
      let u := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
      C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C := by
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let I : ℕ → ℝ := fun k ↦
    ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽
  let r : ℕ → ℝ := fun k ↦ Real.sqrt (I k)
  have hnorm_sq : ∀ j : SpectralLineJetIndex χ a s,
      ‖(spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))‖ ^ 2 = I j.val.2.2 := by
    intro j
    let u := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
    have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(0, 0, s)) := spectralJet_lp_norm_sq u
    have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(0, 0, s)) =
        ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2.2) ∂(L2μ'(0, 0, s)) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (spectralLineJet_memLp χ hs j)] with g hg
      rw [hg, spectralZeroJet_norm_sq]
      simp
    have h3 : ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2.2) ∂(L2μ'(0, 0, s)) = I j.val.2.2 := by
      have hdens : Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) := by
        simpa only [neg_zero] using symmIntervalSobolevDensity_inv_continuous (F := F) le_rfl s
      rw [integral_withDensity_eq_integral_toReal_smul hdens.measurable.ennreal_ofReal
        (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
      dsimp only
      have hdeq : (intervalSobolevDensity 0 0 s (logNorm g))⁻¹ =
          ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ := by
        simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
      rw [smul_eq_mul, hdeq,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le),
        mul_comm]
    exact h1.trans (h2.trans h3)
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, (r k + (r k)⁻¹)
  have hC_pos : 0 < C := by
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.sum_nonneg fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    linarith
  refine ⟨C, hC_pos, fun j ↦ ?_⟩
  have hjN : j.val.2.2 ∈ Finset.range N :=
    Finset.mem_range.mpr (lt_of_lt_of_le j.property (min_le_right _ _))
  have hr_pos : 0 < r j.val.2.2 :=
    Real.sqrt_pos.mpr (spectralLineJet_integral_pos hs (Finset.mem_range.mp hjN))
  have hnorm_eq : ‖(spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))‖ = r j.val.2.2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm_sq j]
  have hterm_le : r j.val.2.2 + (r j.val.2.2)⁻¹ ≤ C := by
    have h1 : r j.val.2.2 + (r j.val.2.2)⁻¹ ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.single_le_sum
        (fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hjN
    linarith
  dsimp only
  rw [hnorm_eq]
  refine ⟨?_, by linarith [inv_pos.mpr hr_pos]⟩
  have hinv_le : (r j.val.2.2)⁻¹ ≤ C := by linarith
  calc
    C⁻¹ ≤ ((r j.val.2.2)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hr_pos) hinv_le
    _ = r j.val.2.2 := inv_inv _

/-- Paper: Terminology 10.2.1.2, p. 444. A regular family has norms bounded
away from zero. -/
def IsRegularSpectralFamily {ι E : Type*} [Norm E] (x : ι → E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ ‖x i‖

/-- Paper: Terminology 10.2.1.2, p. 444. A family is normalized if its
norms are bounded above and the family is regular. -/
def IsNormalizedSpectralFamily {ι E : Type*} [Norm E] (x : ι → E) : Prop :=
  (∃ C : ℝ, ∀ i, ‖x i‖ ≤ C) ∧ IsRegularSpectralFamily x

/-- Paper: Terminology 10.2.1.2, p. 444. On normed-space sequences the
two conditions agree with the existing §4.1 terminology. -/
theorem spectralFamily_regular_normalized_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x : ℕ → E) :
    (IsRegularSpectralFamily x ↔ SchauderBasis.IsRegular x) ∧
    (IsNormalizedSpectralFamily x ↔ SchauderBasis.IsNormalized x) := by
  have hr : IsRegularSpectralFamily x ↔ SchauderBasis.IsRegular x := by
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨Metric.ball 0 c, Metric.ball_mem_nhds _ hc, fun n hn ↦
        (h n).not_gt (by simpa only [Metric.mem_ball, dist_zero_right] using hn)⟩
    · rintro ⟨U, hU, hx⟩
      obtain ⟨c, hc, hball⟩ := Metric.mem_nhds_iff.mp hU
      refine ⟨c, hc, fun n ↦ le_of_not_gt fun hn ↦ hx n (hball ?_)⟩
      simpa only [Metric.mem_ball, dist_zero_right] using hn
  refine ⟨hr, ?_⟩
  simp only [IsNormalizedSpectralFamily, SchauderBasis.IsNormalized, ← hr,
    NormedSpace.isVonNBounded_iff' ℂ, Set.forall_mem_range]
  exact and_comm

/-- Paper: Terminology 10.2.1.2, p. 444. A nonzero vector defines a regular
and normalized singleton family.
Deviation: Sanity check for the two predicates. -/
theorem spectralFamily_singleton_normalized {E : Type*} [NormedAddCommGroup E] (x : E)
    (_hx : x ≠ 0) : IsNormalizedSpectralFamily (fun _ : Unit ↦ x) := by
  exact ⟨⟨‖x‖, fun _ ↦ le_rfl⟩, ‖x‖, norm_pos_iff.mpr _hx, fun _ ↦ le_rfl⟩

-- TODO(paper-gap): The general claim about the Schauder property on p. 444
-- lacks a proof. The primal normalization invoked again on p. 451 is false:
-- close simple critical-line zeta zeros give jets at distance tending to zero,
-- so the corresponding biorthogonal vector norms are unbounded (ERRATA R5).

section BandProjections

attribute [local instance] instDualMeasurableSpaceSec3

/-- Orthogonal projections onto closures of subspaces converge strongly whenever each
vector has a convergent sequence of approximants in the corresponding subspaces. -/
private theorem spectralLineIsotype_bandProjections_of_approximants
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (S : ℕ → Submodule ℂ Q)
    (happrox : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ S n) ∧ Tendsto y atTop (𝓝 q)) :
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (S n : Set Q)) ∧
      (∀ n q y, y ∈ closure (S n : Set Q) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  let C (n : ℕ) := (S n).topologicalClosure
  let : ∀ n, CompleteSpace (C n) := fun n ↦
    (Submodule.isClosed_topologicalClosure (S n)).completeSpace_coe
  let P (n : ℕ) : Q →L[ℂ] Q := (C n).starProjection
  have hmin (n : ℕ) (q y : Q) (hy : y ∈ closure (S n : Set Q)) :
      ‖q - P n q‖ ≤ ‖q - y‖ := by
    change ‖q - (C n).starProjection q‖ ≤ ‖q - y‖
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
      (⟨y, hy⟩ : C n)
  refine ⟨P, ?_, hmin, ?_⟩
  · intro n
    change ((C n).starProjection.range : Set Q) = closure (S n : Set Q)
    rw [Submodule.range_starProjection]
    rfl
  · intro q
    obtain ⟨y, hy, hlim⟩ := happrox q
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (tendsto_iff_dist_tendsto_zero.mp hlim)
    calc
      dist (P n q) q = ‖q - P n q‖ := by
        simpa only [dist_eq_norm] using norm_sub_rev (P n q) q
      _ ≤ ‖q - y n‖ := hmin n q (y n) (subset_closure (hy n))
      _ = dist (y n) q := by
        simpa only [dist_eq_norm] using norm_sub_rev q (y n)

/-- A Fourier band defines a submodule, and its image under a linear quotient map
agrees with the description using any almost-everywhere equal L² representative. -/
private theorem spectralLineIsotype_bandProjections_band_submodule
    {X Y E Q : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup Q] [Module ℂ Q]
    (μ : Measure X) (ν : Measure Y)
    (r : E → X → ℂ) (J : E →ₗ[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] r f)
    (q : E →ₗ[ℂ] Q) (U : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν) (band : Set Y) :
    ∃ S : Submodule ℂ Q, (S : Set Q) =
      {z : Q | ∃ f : E, z = q f ∧ ∃ u : Lp ℂ 2 μ,
        (u : X → ℂ) =ᵐ[μ] r f ∧ ∀ᵐ ψ ∂ν, ψ ∉ band → U u ψ = 0} := by
  let A : Submodule ℂ (Lp ℂ 2 ν) := {
    carrier := {v | ∀ᵐ ψ ∂ν, ψ ∉ band → v ψ = 0}
    zero_mem' := by
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := ν)] with ψ hψ
      exact fun _ ↦ hψ
    add_mem' := by
      intro v w hv hw
      change ∀ᵐ ψ ∂ν, ψ ∉ band → (v + w) ψ = 0
      filter_upwards [Lp.coeFn_add v w, hv, hw] with ψ hψ hvψ hwψ
      intro hψband
      rw [hψ, Pi.add_apply, hvψ hψband, hwψ hψband, add_zero]
    smul_mem' := by
      intro c v hv
      change ∀ᵐ ψ ∂ν, ψ ∉ band → (c • v) ψ = 0
      filter_upwards [Lp.coeFn_smul c v, hv] with ψ hψ hvψ
      intro hψband
      rw [hψ, Pi.smul_apply, hvψ hψband, smul_zero]
  }
  refine ⟨(A.comap (U.comp J)).map q, ?_⟩
  ext z
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, rfl, J f, hJ f, hf⟩
  · rintro ⟨f, rfl, u, hu, hUu⟩
    refine ⟨f, ?_, rfl⟩
    have heq : u = J f := Lp.ext (hu.trans (hJ f).symm)
    change ∀ᵐ ψ ∂ν, ψ ∉ band → U (J f) ψ = 0
    simpa only [heq] using hUu

/-- Set-valued version of the projection argument, allowing the Fourier-band submodules
to be constructed independently from their concrete sets. -/
private theorem spectralLineIsotype_bandProjections_of_sets
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (B : ℕ → Set Q) (hsub : ∀ n, ∃ S : Submodule ℂ Q, (S : Set Q) = B n)
    (happrox : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ B n) ∧ Tendsto y atTop (𝓝 q)) :
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (B n)) ∧
      (∀ n q y, y ∈ closure (B n) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  choose S hS using hsub
  have happrox' : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ S n) ∧ Tendsto y atTop (𝓝 q) := by
    intro q
    obtain ⟨y, hy, hlim⟩ := happrox q
    refine ⟨y, fun n ↦ ?_, hlim⟩
    change y n ∈ (S n : Set Q)
    rw [hS n]
    exact hy n
  obtain ⟨P, hrange, hmin, hlim⟩ :=
    spectralLineIsotype_bandProjections_of_approximants S happrox'
  refine ⟨P, fun n ↦ ?_, fun n q y hy ↦ ?_, hlim⟩
  · simpa only [hS n] using hrange n
  · apply hmin n q y
    simpa only [hS n] using hy

/-- A surjective continuous linear image of supported approximants admits strongly
convergent orthogonal projections onto the closures of the corresponding bands. -/
private theorem spectralLineIsotype_bandProjections_of_supported_approximants
    {X Y E Q : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (μ : Measure X) (ν : Measure Y)
    (r : E → X → ℂ) (J : E →ₗ[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] r f)
    (q : E →L[ℂ] Q) (hq : Surjective q)
    (U : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν) (band : ℕ → Set Y)
    (R : ℕ → E → E)
    (hsupport : ∀ n f, ∀ᵐ ψ ∂ν, ψ ∉ band n → U (J (R n f)) ψ = 0)
    (hlim : ∀ f, Tendsto (fun n ↦ R n f) atTop (𝓝 f)) :
    let B (n : ℕ) := {z : Q | ∃ f : E, z = q f ∧ ∃ u : Lp ℂ 2 μ,
      (u : X → ℂ) =ᵐ[μ] r f ∧ ∀ᵐ ψ ∂ν, ψ ∉ band n → U u ψ = 0}
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (B n)) ∧
      (∀ n z y, y ∈ closure (B n) → ‖z - P n z‖ ≤ ‖z - y‖) ∧
      ∀ z, Tendsto (fun n ↦ P n z) atTop (𝓝 z) := by
  intro B
  have hmem (n : ℕ) (f : E) : q (R n f) ∈ B n :=
    ⟨R n f, rfl, J (R n f), hJ (R n f), hsupport n f⟩
  have happrox (z : Q) : ∃ y : ℕ → Q,
      (∀ n, y n ∈ B n) ∧ Tendsto y atTop (𝓝 z) := by
    obtain ⟨f, rfl⟩ := hq z
    refine ⟨fun n ↦ q (R n f), fun n ↦ hmem n f, ?_⟩
    exact q.continuous.continuousAt.tendsto.comp (hlim f)
  have hsub (n : ℕ) : ∃ S : Submodule ℂ Q, (S : Set Q) = B n := by
    exact spectralLineIsotype_bandProjections_band_submodule μ ν r J hJ
      q.toLinearMap U (band n)
  exact spectralLineIsotype_bandProjections_of_sets B hsub happrox

private theorem spectralLineIsotype_bandProjections_support_closed
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (S : Set X)
    (hS : MeasurableSet S) :
    IsClosed {f : Lp ℂ 2 ν | ∀ᵐ x ∂ν, x ∉ S → f x = 0} := by
  obtain ⟨P, -, hP⟩ := hardySobolevCutoff_spec (μ := ν) hS
  have hset : {f : Lp ℂ 2 ν | ∀ᵐ x ∂ν, x ∉ S → f x = 0} =
      {f : Lp ℂ 2 ν | P f = f} := by
    ext f
    constructor
    · intro hf
      apply Lp.ext
      filter_upwards [(hP f).2.2, hf] with x hx hfx
      rw [hx]
      by_cases hxs : x ∈ S
      · exact Set.indicator_of_mem hxs _
      · rw [Set.indicator_of_notMem hxs, hfx hxs]
    · intro hf
      filter_upwards [(hP f).2.2] with x hx
      intro hxs
      rw [hf] at hx
      exact hx.trans (Set.indicator_of_notMem hxs _)
  rw [hset]
  exact isClosed_eq P.continuous continuous_id

private theorem spectralLineIsotype_bandProjections_dense_integrable
    {G : Type*} [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
    [NormalSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ w : Measure G)
    [IsLocallyFiniteMeasure μ] [w.Regular] (hle : μ ≤ w) :
    Dense {u : Lp ℂ 2 w | Integrable (u : G → ℂ) μ} := by
  intro u
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hlt⟩ := exists_between hε
  obtain ⟨f, hc, he, hf, hm⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le (by simp) hr.ne'
  refine ⟨hm.toLp f,
    (hf.integrable_of_hasCompactSupport hc).congr (ae_mono hle hm.coeFn_toLp.symm), ?_⟩
  rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
  exact he.trans_lt hlt

private theorem spectralLineIsotype_bandProjections_convolution_support
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) (w : Measure G) [w.Regular]
    (hle : μ ≤ w) (J : Lp ℂ 2 w →L[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[μ] (u : G → ℂ))
    (τ : G →* (Lp ℂ 2 w →L[ℂ] Lp ℂ 2 w))
    (hτ : ∀ g u, (τ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x))
    (hcτ : Continuous (fun z : G × Lp ℂ 2 w ↦ τ z.1 z.2))
    (φ : G → ℂ) (hφ : Integrable φ μ) (A : Lp ℂ 2 w →L[ℂ] Lp ℂ 2 w)
    (hA : ∀ u, HasPettisIntegral (.positive μ) (fun g ↦ φ g • τ g u) (A u))
    (u : Lp ℂ 2 w) :
    ∀ᵐ ψ ∂ν, ψ ∉ tsupport (lcaFourier μ φ) →
      (lcaFourier_unitary μ ν hν).exists.choose (J (A u)) ψ = 0 := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let U := (lcaFourier_unitary μ ν hν).exists.choose
  let S := tsupport (lcaFourier μ φ)
  have hclosed : IsClosed {u : Lp ℂ 2 w |
      ∀ᵐ ψ ∂ν, ψ ∉ S → U (J (A u)) ψ = 0} :=
    (spectralLineIsotype_bandProjections_support_closed ν S
      (isClosed_tsupport _).measurableSet).preimage
      (U.continuous.comp (J.continuous.comp A.continuous))
  have hD := spectralLineIsotype_bandProjections_dense_integrable μ w hle
  apply hclosed.closure_subset_iff.mpr ?_ (hD u)
  intro z hz
  let f := lcaConvolution μ φ z
  have hv : (J (A z) : G → ℂ) =ᵐ[μ] f :=
    pettis_convolution_haar_L2 μ J hJ τ hτ hcτ φ hφ z (A z) (hA z)
  have hf : MemLp f 2 μ := (Lp.memLp (J (A z))).ae_eq hv
  have heq : J (A z) = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  have hFourier : (U (J (A z)) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
    rw [heq]
    exact (lcaFourier_unitary μ ν hν).exists.choose_spec f
      (lcaConvolution_integrable μ hφ hz).2.1 hf
  filter_upwards [hFourier] with ψ hψ
  intro hψS
  rw [hψ, show lcaFourier μ f = _ from lcaFourier_convolution μ hφ hz,
    Pi.mul_apply, image_eq_zero_of_notMem_tsupport hψS, zero_mul]

private theorem spectralLineIsotype_bandProjections_zeroLine_support
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (s : ℝ) (hs : 0 ≤ s)
    (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose
    let U := (lcaFourier_unitary μ ν hν).exists.choose
    ∃ J : W →L[ℂ] Lp ℂ 2 μ,
      (∀ u, (J u : G → ℂ) =ᵐ[μ] (u : G → ℂ)) ∧
      ∀ (φ : SchwartzBruhat G) (u : W), ∀ᵐ ψ ∂ν,
        ψ ∉ tsupport (lcaFourier μ φ) → U (J (A φ u)) ψ = 0 := by
  intro W A U
  let w := μ.withDensity fun x ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 s (Real.log ((m x).val : ℝ)))
  have hle : μ ≤ w := by
    calc
      μ = μ.withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun x ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  let : IsLocallyFiniteMeasure w := IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_intervalSobolevDensity 0 0 s).comp (continuous_logModule' m))
  obtain ⟨J, hJ⟩ := exists_L2_restriction w μ hle
  refine ⟨J, hJ, ?_⟩
  intro φ u
  exact spectralLineIsotype_bandProjections_convolution_support μ ν hν w hle J hJ
    (hardySobolevTranslation μ m 0 0 s le_rfl hs)
    (hardySobolevTranslation_apply μ m 0 0 s le_rfl hs)
    (exists_hardySobolevTranslation μ m 0 0 s le_rfl hs).choose_spec.2
    (φ : G → ℂ) ((schwartzBruhat_fourier_equiv μ).choose_spec φ).1 (A φ)
    ((existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose_spec φ) u

/-- Paper: Remark 10.2.1.5, p. 444. The projections on the isotypic quotient
onto the closures of the images of the Fourier bands converge strongly to
the identity. Each orthogonal projection selects a closest element of its range.
Deviation: The Fourier bands use the inverse lift for left translation. -/
theorem spectralLineIsotype_bandProjections (χ : PontryaginDual C𝔽) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) (ν : Measure (PontryaginDual C𝔽)) (hν : IsLCAPlancherelMeasure μ𝔽 ν) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let ω := χ.comp restriction
    let E := Wω(hI, hs, ω)
    let N := (Θ(a, hI, hs)).comap E.subtype
    let Q := spectralSobolevIsotypeQuotient F a hI hs ω
    let U := (lcaFourier_unitary μ𝔽 ν hν).exists.choose
    let B (n : ℕ) := {q : Q | ∃ f : E,
      q = N.mkQ f ∧ ∃ u : Lp ℂ 2 μ𝔽, (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f.val : C𝔽 → ℂ) ∧
        ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n → U u ψ = 0}
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, range (P n) = closure (B n)) ∧
      (∀ n q y, y ∈ closure (B n) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  intro hI ω E N Q U B
  have hrestriction :=
    spectralLineIsotype_bandProjections_zeroLine_support (G := C𝔽) μ𝔽 m𝔽 s hs ν hν
  let J := hrestriction.choose
  have hJ := hrestriction.choose_spec.1
  have hJsupp := hrestriction.choose_spec.2
  have hconvolution := exists_spectralLineIsotypeConvolution (F := F) χ hs
  let φ := hconvolution.choose
  let R := hconvolution.choose_spec.choose
  have hband := hconvolution.choose_spec.choose_spec.2.2.1
  have hR := hconvolution.choose_spec.choose_spec.2.2.2.1
  have hlim := hconvolution.choose_spec.choose_spec.2.2.2.2
  have hsupported (n : ℕ) (f : E) :
      ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n →
        U (J (R n f).val) ψ = 0 := by
    have hsupp := hJsupp (φ n) f.val
    rw [hR n f]
    filter_upwards [hsupp] with ψ hψ
    intro hψband
    exact hψ (fun hψsupp ↦ hψband (hband n hψsupp))
  let hEclosed : IsClosed (E : Set W(0, 0, s)) :=
    instClosedSpectralIsotypeSec2 (F := F) hI hs ω
  let : CompleteSpace E := hEclosed.completeSpace_coe
  let hNclosed : IsClosed (N : Set E) :=
    instClosedSpectralIsotypeThetaSec2 (F := F) a hI hs ω
  let : CompleteSpace N := hNclosed.completeSpace_coe
  exact spectralLineIsotype_bandProjections_of_supported_approximants
    (X := C𝔽) (Y := PontryaginDual C𝔽) (E := E) (Q := Q)
    μ𝔽 ν (fun f : E ↦ (f.val : C𝔽 → ℂ))
    (J.toLinearMap.comp E.subtype) (fun f ↦ hJ f.val)
    N.mkQL N.mkQ_surjective U.toLinearEquiv.toLinearMap
    (fun n ↦ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n)
    (fun n f ↦ R n f) hsupported hlim

end BandProjections

/-- Paper: (10.2.2.5)–(10.2.2.6), p. 446. Keep the full multiplicity in
the strip interior and apply the boundary cutoff at the two endpoints.
Deviation: Extend by zero off the strip and use the strict boundary cutoff. -/
def spectralStripMultiplicity (α s b : ℝ) (N : ℕ) : ℕ :=
  if -α < b ∧ b < α then N
  else if b = -α ∨ b = α then spectralBoundaryMultiplicity s N else 0

/-- Paper: (10.2.2.5), p. 446. At either boundary the strip multiplicity
is the truncated multiplicity. -/
theorem spectralStripMultiplicity_boundary {α b : ℝ} (_hα : 0 ≤ α)
    (_hb : b = -α ∨ b = α) (s : ℝ) (N : ℕ) :
    spectralStripMultiplicity α s b N = spectralBoundaryMultiplicity s N := by
  unfold spectralStripMultiplicity
  split_ifs with h1
  · exfalso
    rcases _hb with rfl | rfl <;> linarith [h1.1, h1.2]
  · rfl

/-- Paper: (10.2.2.6), p. 446. At an interior point every order below the
zero multiplicity is retained. -/
theorem spectralStripMultiplicity_interior {α b : ℝ} (_hb : b ∈ Ioo (-α) α) (s : ℝ) (N : ℕ) :
    spectralStripMultiplicity α s b N = N := by
  unfold spectralStripMultiplicity
  rw [mem_Ioo] at _hb
  simp [_hb]

/-- Paper: Theorem 10.2.2.1, p. 446. Index the strip jets by the norm-one
component, real offset, ordinate, and surviving derivative order. The point
of evaluation has real part a+b. -/
abbrev SpectralStripJetIndex (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a α s : ℝ) :=
  {j : PontryaginDual C₁ × ℝ × ℝ × ℕ //
    j.2.2.2 < spectralStripMultiplicity α s j.2.1
      (multiplicity(χ j.1, shift(a + j.2.1, j.2.2.1)))}

/-- Paper: Theorem 10.2.2.1, p. 446. Every strip jet is indexed by a
point in the closed strip and that point is a zero of the completed L-function. -/
theorem SpectralStripJetIndex.mem_strip_order_pos {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    {a α s : ℝ} (_hα : 0 ≤ α) (j : SpectralStripJetIndex χ a α s) :
    j.val.2.1 ∈ Icc (-α) α ∧
      0 < vanishingOrder(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1)) := by
  have key : ∀ o : WithTop ℤ, 0 < o.untop₀.toNat → 0 < o := by
    intro o h
    cases o with
    | top => simp at h
    | coe n =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < n)
  have h := j.2
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
  split_ifs at h with h1 h2
  · exact ⟨⟨h1.1.le, h1.2.le⟩, key _ (by omega)⟩
  · refine ⟨?_, key _ (by omega)⟩
    rw [mem_Icc]
    rcases h2 with h2 | h2 <;> constructor <;> linarith
  · omega

private theorem integrable_exp_neg_abs_mul_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) volume := by
  have hcont : Continuous (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul (continuous_id.pow (2 * k))
  let M : ℝ := ((2 * k).factorial : ℝ) / c ^ (2 * k) +
    ((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)
  have hdom : Integrable (fun x : ℝ ↦ M * (1 + x ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul M
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hnonneg : 0 ≤ Real.exp (-c * |x|) * x ^ (2 * k) :=
    mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x)
  rw [Real.norm_of_nonneg hnonneg]
  have hu : 0 ≤ c * |x| := mul_nonneg hc.le (abs_nonneg x)
  have h1 : (c * |x|) ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.exp (c * |x|) :=
    Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k)
  have h2 : (c * |x|) ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) ≤ Real.exp (c * |x|) :=
    Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k + 2)
  have hfac1 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hfac2 : (0 : ℝ) < ((2 * k + 2).factorial : ℝ) := by positivity
  have hc1 : 0 < c ^ (2 * k) := pow_pos hc _
  have hc2 : 0 < c ^ (2 * k + 2) := pow_pos hc _
  have hpow1 : x ^ (2 * k) ≤ (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac1).mp h1]
    have hxa : |x| ^ (2 * k) = x ^ (2 * k) := by
      rw [pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
    linarith
  have hpow2 : x ^ (2 * k) * x ^ 2 ≤
      (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k + 2) ≤ ((2 * k + 2).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac2).mp h2]
    have hxa : |x| ^ (2 * k + 2) = x ^ (2 * k) * x ^ 2 := by
      rw [pow_add, pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    linarith
  have hsum : x ^ (2 * k) * (1 + x ^ 2) ≤ M * Real.exp (c * |x|) := by
    have : x ^ (2 * k) * (1 + x ^ 2) = x ^ (2 * k) + x ^ (2 * k) * x ^ 2 := by ring
    rw [this]
    have : M * Real.exp (c * |x|) =
        (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) +
        (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
      dsimp only [M]
      ring
    linarith
  have hexp_neg : Real.exp (-c * |x|) = (Real.exp (c * |x|))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hexp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _), mul_comm (M * _), ← mul_assoc]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  linarith

private theorem stripJet_integrand_continuous (α s b : ℝ) (k : ℕ) :
    Continuous (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub (continuous_const.mul continuous_abs))).mul
    (continuous_id.pow (2 * k))).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem stripJet_integrand_eq {α : ℝ} (hα : 0 ≤ α) (s b : ℝ) (k : ℕ) (x : ℝ) :
    Real.exp (2 * b * x) * x ^ (2 * k) * (intervalSobolevDensity (-α) α s x)⁻¹ =
      Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
  rw [symmIntervalSobolevDensity_eq hα, mul_inv, Real.exp_sub, div_eq_mul_inv]
  ring

private theorem spectralStripJet_integrable {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {k : ℕ}
    (h : (-α < b ∧ b < α) ∨ ((b = -α ∨ b = α) ∧ 2 * (k : ℝ) + 1 < s)) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  rcases h with ⟨hb1, hb2⟩ | ⟨hb, hk⟩
  · have hδ : 0 < α - |b| := by
      have : |b| < α := abs_lt.mpr ⟨hb1, hb2⟩
      linarith
    refine (integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * (α - |b|)) k).mono'
      (stripJet_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg]
    have hbx : b * x ≤ |b| * |x| := by
      calc
        b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ Real.exp (-(2 * (α - |b|)) * |x|) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
    calc
      Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
        ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * 1 :=
          mul_le_mul_of_nonneg_left hinv_le
            (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
      _ = Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) := mul_one _
      _ ≤ Real.exp (-(2 * (α - |b|)) * |x|) * x ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hexp (Even.pow_nonneg (even_two_mul k) x)
  · refine (integrable_pow_mul_rpow_inv hk).mono'
      (stripJet_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg, mul_assoc]
    have hba : |b| = α := by
      rcases hb with rfl | rfl
      · rw [abs_neg, abs_of_nonneg hα]
      · exact abs_of_nonneg hα
    have hbx : b * x ≤ α * |x| := by
      calc
        b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
        _ = α * |x| := by rw [hba]
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      Real.exp (2 * b * x - 2 * α * |x|) * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
        ≤ 1 * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
              (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
      _ = x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _

/-- Paper: Theorem 10.2.2.1, p. 446. The admitted strip jets are
square-integrable for the reciprocal strip weight.
Deviation: Exclude the divergent boundary endpoint of (10.2.2.5). -/
theorem spectralStripJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s) :
    MemLp (stripJet(χ, j)) 2 (L2μ'(-α, α, s)) := by
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hν : Integrable (fun g : C𝔽 ↦
      Real.exp (2 * j.val.2.1 * logNorm g - 2 * α * |logNorm g|) *
        (logNorm g) ^ (2 * j.val.2.2.2) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) ν :=
    (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).integrable_comp_of_integrable
      (spectralStripJet_integrable _hα _hs hcond)
  have hμ : Integrable (fun g : C𝔽 ↦
      Real.exp (2 * j.val.2.1 * logNorm g - 2 * α * |logNorm g|) *
        (logNorm g) ^ (2 * j.val.2.2.2) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) μ𝔽 := by
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact hν.smul_measure_nnreal
  apply (memLp_two_iff_integrable_sq_norm
    (spectralZeroJet_continuous (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2).aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    ((symmIntervalSobolevDensity_inv_continuous _hα s).measurable.ennreal_ofReal)
    (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ𝔽 fun g ↦ ?_)
  dsimp only
  rw [spectralZeroJet_norm_sq,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos _hα s (logNorm g)).le),
    stripJet_integrand_eq _hα]

local notation "stripI(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripU(" χ ", " hα ", " hs ")" =>
  (fun j ↦ (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)))

section StripThetaAnnihilation

local notation "ℬ" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))

/-- Factorization on a right half-plane determines the equality of meromorphic
orders everywhere. -/
private theorem stripTheta_order_of_factor {Z L A : ℂ → ℂ} (hZ : Differentiable ℂ Z)
    (hL : MeromorphicOn L univ) (hA : AnalyticOnNhd ℂ A univ)
    (heq : ∀ z : ℂ, 1 < z.re → Z z = L z * A z) (w : ℂ) :
    meromorphicOrderAt Z w = meromorphicOrderAt L w + meromorphicOrderAt A w := by
  have hLA : MeromorphicOn (L * A) univ := hL.mul (fun z hz ↦ (hA z hz).meromorphicAt)
  have hzM : MeromorphicOn Z univ := fun z _ ↦ (hZ.analyticAt z).meromorphicAt
  have hd : MeromorphicOn (Z - L * A) univ := hzM.sub hLA
  have ho : meromorphicOrderAt (Z - L * A) 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with z hz using sub_eq_zero.mpr (heq z hz)
  have hw := hd.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ w) ho
  have he : Z =ᶠ[𝓝[≠] w] L * A :=
    (meromorphicOrderAt_eq_top_iff.mp hw).mono fun z hz ↦ sub_eq_zero.mp hz
  rw [meromorphicOrderAt_congr he, meromorphicOrderAt_mul (hL w (mem_univ w)) (hA w (mem_univ w)).meromorphicAt]

private theorem stripTheta_deriv_of_order {Z L : ℂ → ℂ} {w : ℂ} (hZ : AnalyticAt ℂ Z w)
    (ho : meromorphicOrderAt L w ≤ meromorphicOrderAt Z w) {k : ℕ}
    (hk : k < (meromorphicOrderAt L w).untop₀.toNat) : iteratedDeriv k Z w = 0 := by
  have hlt : (k : WithTop ℤ) < meromorphicOrderAt L w := by
    cases h : meromorphicOrderAt L w with
    | top => simp
    | coe n =>
      rw [h, WithTop.untop₀_coe] at hk
      exact WithTop.coe_lt_coe.mpr (by omega)
  have hl := hlt.trans_le ho
  rw [hZ.meromorphicOrderAt_eq] at hl
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := k+1) hZ).mp _ k (Nat.lt_succ_self k)
  cases h : analyticOrderAt Z w with
  | top => simp
  | coe n =>
    rw [h, ENat.map_natCast] at hl
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast (show (k : ℤ) < n from WithTop.coe_lt_coe.mp hl))

/-- The normalized eigendistribution is the entire test factor and the two
orders add at every point. -/
private theorem stripTheta_mellin_factor_order (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (w : ℂ) :
    let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
    let L := continuedCompletedHeckeL χ
    let Φ := fun z ↦ (adelicEigendistribution_normalized χ).choose z f.val
    AnalyticAt ℂ Φ w ∧ meromorphicOrderAt Z w = meromorphicOrderAt L w + meromorphicOrderAt Φ w := by
  let Z (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  let L := continuedCompletedHeckeL χ
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hZ : Differentiable ℂ Z := globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ
  let D := (adelicEigendistribution_normalized χ).choose
  have hD := (adelicEigendistribution_normalized χ).choose_spec
  let d : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  let A (z : ℂ) := d * D z f.val
  have hE : AnalyticOnNhd ℂ (fun z ↦ D z f.val) univ := by
    let e : StrongDual ℂ ℬ →L[ℂ] ℂ := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) f.val
    have hE : Differentiable ℂ (e ∘ D) := by
      intro z
      have hd := hD.1.hasFDerivAt (isOpen_univ.mem_nhds (mem_univ z))
      have he : HasFDerivAt (e ∘ D) (e.comp (fderiv ℂ D z)) z := by
        apply HasFDerivAt.of_isLittleOTVS
        simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
          using e.isBigOTVS_comp.trans_isLittleOTVS hd.isLittleOTVS
      exact he.differentiableAt
    exact fun z _ ↦ hE.analyticAt z
  have hA : AnalyticOnNhd ℂ A univ := analyticOnNhd_const.mul hE
  have hσ (ψ : PontryaginDual C𝔽) (z : ℂ) := quasiCharacterAbscissa_of_unitary_twist
    (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
    (ideleClassNormTwist ψ z) ψ z (fun _ ↦ rfl)
  have hfact (z : ℂ) (hz : 1 < z.re) : Z z = L z * A z := by
    let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
    have h0 : σ 1 = 0 := by
      change Real.log ‖(1 : ℂ)‖ / _ = 0
      rw [norm_one, Real.log_one, zero_div]
    have hn : ideleClassNormTwist χ z ≠ 1 := fun h ↦ (zero_lt_one.trans hz).ne'
      ((hσ χ z).symm.trans ((congrArg σ h).trans h0))
    have hn' : ideleClassNormTwist χ z ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 :=
      fun h ↦ hz.ne' ((hσ χ z).symm.trans ((congrArg σ h).trans (hσ _ 1)))
    have hzeta := congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf hf')
      (ideleClassNormTwist χ z)
    refine hzeta.trans ((hD.2.2 z hn hn' f.val).trans ?_)
    rw [gaussianCompletedHeckeL_eq_completedHeckeL χ z hz]
    have h := (continuedCompletedHeckeL_spec χ).2 ⟨z,hz⟩
    change d * completedHeckeL χ ⟨z,hz⟩ * D z f.val = L z * (d * D z f.val)
    rw [← h]
    ring
  have he := stripTheta_order_of_factor hZ (continuedCompletedHeckeL_spec χ).1.meromorphicOn hA hfact w
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F))).ne')
  have ha : meromorphicOrderAt A w = meromorphicOrderAt (fun z ↦ D z f.val) w :=
    meromorphicOrderAt_mul_of_ne_zero (g := fun _ ↦ d) analyticAt_const hd
  exact ⟨hE w (mem_univ w), he.trans (congrArg (meromorphicOrderAt L w + ·) ha)⟩

/-- The completed L-function divides each polar-free theta Mellin transform as
a germ; equality of orders holds wherever the normalized eigendistribution is nonzero. -/
private theorem stripTheta_mellin_order (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (w : ℂ) :
    let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
    let L := continuedCompletedHeckeL χ
    meromorphicOrderAt L w ≤ meromorphicOrderAt Z w ∧
      ((adelicEigendistribution_normalized χ).choose w f.val ≠ 0 →
        meromorphicOrderAt Z w = meromorphicOrderAt L w) := by
  obtain ⟨hA, he⟩ := stripTheta_mellin_factor_order χ f w
  refine ⟨(le_add_of_nonneg_right hA.meromorphicOrderAt_nonneg).trans he.symm.le, fun hu ↦ ?_⟩
  exact he.trans (by rw [hA.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hu, add_zero])

/-- The Mellin derivatives below the completed L-function’s order vanish. -/
private theorem stripTheta_mellin_zero (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (w : ℂ) (k : ℕ) (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) w).untop₀.toNat) :
    iteratedDeriv k (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w = 0 := by
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  exact stripTheta_deriv_of_order (globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ |>.analyticAt w)
    (stripTheta_mellin_order χ f w).1 hk

/-- Two translation differences kill the polar coordinates while preserving a
nonzero eigenfunctional of any distinct weight. -/
private theorem polarShift_preserve {E G : Type*} [AddCommGroup E] [Module ℂ E]
    (P : E →ₗ[ℂ] ℂ × ℂ) (D : E →ₗ[ℂ] ℂ) (τ : G → E → E) (c₀ c₁ c : G → ℂ)
    (hp₀ : ∀ g f, (P (τ g f)).1 = c₀ g * (P f).1)
    (hp₁ : ∀ g f, (P (τ g f)).2 = c₁ g * (P f).2)
    (hd : ∀ g f, D (τ g f) = c g * D f) (f : E) (hf : D f ≠ 0)
    {g h : G} (hg : c g ≠ c₀ g) (hh : c h ≠ c₁ h) : ∃ f' : P.ker, D f'.val ≠ 0 := by
  let x := τ g f - c₀ g • f
  let y := τ h x - c₁ h • x
  have h₀ : (P x).1 = 0 := by simp [x, hp₀]
  have hP : P y = 0 := by
    ext <;> simp [y, hp₀, hp₁, h₀]
  refine ⟨⟨y, hP⟩, ?_⟩
  have hval : D y = (c h - c₁ h) * (c g - c₀ g) * D f := by
    simp [y, x, hd]
    ring
  exact hval ▸ mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hh) (sub_ne_zero.mpr hg)) hf

private theorem stripTheta_normalized_nonzero_on_polar (χ : PontryaginDual C𝔽) (w : ℂ)
    (h₀ : ideleClassNormTwist χ w ≠ 1)
    (h₁ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F, (adelicEigendistribution_normalized χ).choose w f.val ≠ 0 := by
  classical
  let c := ideleClassNormTwist χ w
  let n := ideleClassNormTwist (1 : PontryaginDual C𝔽) 1
  let D := (adelicEigendistribution_normalized χ).choose w
  have hD := ((adelicEigendistribution_normalized χ).choose_spec.2.1 w D).mp rfl
  let π : IdeleGroup (𝓞 F) F → C𝔽 := QuotientGroup.mk
  have hsep (d : QuasiCharacter C𝔽) (hne : c ≠ d) : ∃ g, c (π g) ≠ d (π g) := by
    by_contra! hall
    apply hne
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact hall g
  obtain ⟨g,hg⟩ := hsep 1 h₀
  obtain ⟨h,hh⟩ := hsep n h₁
  let P := adelePolarValues (F := F)
  let τ := schwartzBruhatUnitTranslate (R := AdeleRing (𝓞 F) F)
  let K := (adelicThetaLinearMap F).ker
  have hact := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
  have hp₀ (g : IdeleGroup (𝓞 F) F) (f : ℬ) : (P (τ g f)).1 = (1 : QuasiCharacter C𝔽) (π g) * (P f).1 := by
    change (τ g f) (Multiplicative.ofAdd 0) = 1 * f (Multiplicative.ofAdd 0)
    rw [schwartzBruhatUnitTranslate_apply, mul_zero, one_mul]
  have hp₁ (g : IdeleGroup (𝓞 F) F) (f : ℬ) : (P (τ g f)).2 = n (π g) * (P f).2 := by
    have hh := globalThetaPolarValues_snd_translate (π g) (K.mkQL f)
    have hraw : (P (τ g f)).2 = ((ideleClassNorm F (π g)).val : ℝ) * (P f).2 :=
      (congrArg (fun x ↦ (globalThetaPolarValues (F := F) x).2) (hact g f).symm).trans hh
    change _ = ((1 : ℂ) * ((((ideleClassNorm F (π g)).val : ℝ) : ℂ) ^ (1 : ℂ))) * _
    simpa only [Complex.cpow_one, one_mul] using hraw
  exact polarShift_preserve P D.toLinearMap τ _ _ _ hp₀ hp₁ hD.1 (adelicStandardGaussian χ)
    (hD.2.trans_ne one_ne_zero) hg hh

/-- Paper: Theorem 3.4.3.3(2), p. 153, and Theorem 10.2.1.1, pp. 441–442.
At each twist away from the trivial character and the idelic norm, one polar-free
test attains the order of the completed Hecke L-function in its Mellin transform. -/
private theorem exists_globalThetaMellinIntegral_order_eq_of_regular (χ : PontryaginDual C𝔽) (w : ℂ)
    (h₀ : ideleClassNormTwist χ w ≠ 1)
    (h₁ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w =
        meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
  obtain ⟨f, hf⟩ := stripTheta_normalized_nonzero_on_polar χ w h₀ h₁
  exact ⟨f, (stripTheta_mellin_order χ f w).2 hf⟩

/-- Paper: Proposition 3.2.1.3(2), p. 123. In a unitary chart the trivial
quasi-character and the idelic norm correspond to simple poles of the completed L-function. -/
private theorem continuedCompletedHeckeL_order_of_exceptional (χ : PontryaginDual C𝔽) (w : ℂ)
    (he : ideleClassNormTwist χ w = 1 ∨
      ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) w = -1 := by
  have h0 : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext1 g
    change 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 : ℂ)) = 1
    simp
  obtain ⟨z, hz, hc⟩ : ∃ z : ℂ, (z = 0 ∨ z = 1) ∧ ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) z := by
    rcases he with he | he
    · exact ⟨0, Or.inl rfl, he.trans h0.symm⟩
    · exact ⟨1, Or.inr rfl, he⟩
  have hres : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext g : 1
    apply Subtype.ext
    have hu := DFunLike.congr_fun hc g.val
    change (χ g.val : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ w) =
      1 * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ z) at hu
    rw [g.property] at hu
    change (χ g.val : ℂ) = 1
    simpa only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one] using hu
  obtain ⟨t, ⟨ht, hp₀, hp₁, _⟩, _⟩ := completedHeckeL_continuation_simplePoles χ _
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hres
  have heq : ideleClassNormTwist (1 : PontryaginDual C𝔽) (-Complex.I * (t : ℂ) + w) =
      ideleClassNormTwist (1 : PontryaginDual C𝔽) z := by
    simpa only [zero_add] using (ideleClassNormTwist_add_of_eq ht w).symm.trans (by simpa only [zero_add] using hc)
  let γ := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 z
  have hγ (u : ℝ≥0ˣ) : γ u = ((u.val : ℝ) : ℂ) ^ z := one_mul _
  have hc' : z = -Complex.I * (t : ℂ) + w := by
    apply (existsUnique_complexPower γ).unique hγ
    intro u
    let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F u)
    have hg : ideleClassNorm F g = u := canonicalIdeleNormSection_rightInverse F u
    have hu := DFunLike.congr_fun heq g
    change 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ) + w)) = 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ z) at hu
    rw [hg, one_mul, one_mul] at hu
    exact (hγ u).trans hu.symm
  rcases hz with rfl | rfl
  · exact (congrArg (meromorphicOrderAt (continuedCompletedHeckeL χ)) (by linear_combination -hc' : w = Complex.I * t)).trans hp₀
  · exact (congrArg (meromorphicOrderAt (continuedCompletedHeckeL χ)) (by linear_combination -hc' : w = 1 + Complex.I * t)).trans hp₁

/-- Paper: Theorem 10.2.1.1, pp. 441–442, and Theorem 10.2.2.1, p. 446.
At every zero of the completed Hecke L-function, some polar-free theta test has
a Mellin transform with exactly its multiplicity. -/
private theorem exists_globalThetaMellinIntegral_order_eq_of_zero (χ : PontryaginDual C𝔽) (w : ℂ)
    (hw : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) w) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w =
        meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
  have hn : ¬ (ideleClassNormTwist χ w = 1 ∨
      ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) := by
    intro h
    rw [continuedCompletedHeckeL_order_of_exceptional χ w h] at hw
    exact (by decide : ¬ (0 : WithTop ℤ) < -1) hw
  exact exists_globalThetaMellinIntegral_order_eq_of_regular χ w (not_or.mp hn).1 (not_or.mp hn).2

/-- Paper: Theorem 10.2.2.1, p. 446, and (3.4.3.15), p. 153. On a polar-free test
the first nonvanishing Mellin derivative can attain the full Hecke multiplicity at
each admitted strip jet.
Deviation: This statement concerns derivatives of the test function's Mellin transform.
Only orders below the strict cutoff give continuous Sobolev moments at the boundary. -/
theorem SpectralStripJetIndex.exists_thetaMellin_first_nonvanishing
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a α s : ℝ} (j : SpectralStripJetIndex χ a α s) :
    let w := shift(a + j.val.2.1, j.val.2.2.1)
    let n := (meromorphicOrderAt (continuedCompletedHeckeL (χ j.val.1)) w).untop₀.toNat
    ∃ f : adelePolarSubspace F,
      let Z := fun u ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist (χ j.val.1) u)
      (∀ k < n, iteratedDeriv k Z w = 0) ∧ iteratedDeriv n Z w ≠ 0 := by
  intro w n
  let L := continuedCompletedHeckeL (χ j.val.1)
  have hn : 0 < n := by
    have h : j.val.2.2.2 < spectralStripMultiplicity α s j.val.2.1 n := j.property
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
    split_ifs at h <;> omega
  have hn' : 0 < meromorphicOrderAt L w ∧ meromorphicOrderAt L w = (n : WithTop ℤ) := by
    change 0 < (meromorphicOrderAt L w).untop₀.toNat at hn
    change 0 < meromorphicOrderAt L w ∧ meromorphicOrderAt L w = ((meromorphicOrderAt L w).untop₀.toNat : WithTop ℤ)
    cases h : meromorphicOrderAt L w with
    | top => simp [h] at hn
    | coe z =>
      rw [h, WithTop.untop₀_coe] at hn
      rw [WithTop.untop₀_coe]
      exact ⟨WithTop.coe_lt_coe.mpr (by omega), WithTop.coe_eq_coe.mpr (by omega)⟩
  obtain ⟨f, hf⟩ := exists_globalThetaMellinIntegral_order_eq_of_zero (χ j.val.1) w hn'.1
  let Z := fun u ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist (χ j.val.1) u)
  obtain ⟨hf₀,hf₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hZ : AnalyticAt ℂ Z w := (globalThetaMellinIntegral_entire_of_vanishing f.val hf₀ hf₁ (χ j.val.1)).analyticAt w
  have hz : meromorphicOrderAt Z w = (n : WithTop ℤ) := hf.trans hn'.2
  rw [hZ.meromorphicOrderAt_eq] at hz
  refine ⟨f, (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hZ).mp ?_⟩
  cases h : analyticOrderAt Z w with
  | top => simp [h] at hz
  | coe r =>
    rw [h, ENat.map_natCast] at hz
    congr 1
    exact_mod_cast (WithTop.coe_eq_coe.mp hz)

/-- A character with nonzero logarithmic derivative crosses each polar weight simply. -/
private theorem stripTheta_polarFactor_order {B : ℂ → ℂ} {w d : ℂ} (hB : AnalyticAt ℂ B w)
    (hD : HasDerivAt B d w) (hd : d ≠ 0) (hw : B w = 1 ∨ B w = 2) :
    meromorphicOrderAt (fun z ↦ (B z - 2) * (B z - 1)) w = 1 := by
  let A := fun z ↦ (B z - 2) * (B z - 1)
  have ha : AnalyticAt ℂ A w := (hB.sub analyticAt_const).mul (hB.sub analyticAt_const)
  have hv : A w = 0 := by rcases hw with h | h <;> simp [A, h]
  have hda : HasDerivAt A (d * (B w - 1) + (B w - 2) * d) w :=
    (hD.sub_const _).mul (hD.sub_const _)
  have hn : deriv A w ≠ 0 := by
    rw [hda.deriv]
    rcases hw with h | h <;> norm_num [h, hd]
  have ho : analyticOrderAt A w = 1 := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := 1) ha).mpr
    ⟨fun k hk ↦ by simpa [Nat.lt_one_iff.mp hk] using hv, by simpa using hn⟩
  change meromorphicOrderAt A w = 1
  rw [ha.meromorphicOrderAt_eq, ho]
  rfl

/-- A double difference of the standard Gaussian removes both polar values. At
either exceptional weight its normalized Mellin factor has a simple zero. -/
private theorem stripTheta_exists_normalized_order_one (χ : PontryaginDual C𝔽) (w : ℂ)
    (he : ideleClassNormTwist χ w = 1 ∨ ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ (adelicEigendistribution_normalized χ).choose z f.val) w = 1 := by
  let r : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let g := canonicalIdeleNormSection F r
  let y : C𝔽 := QuotientGroup.mk g
  have hy : ideleClassNorm F y = r := canonicalIdeleNormSection_rightInverse F r
  let τ := schwartzBruhatUnitTranslate (R := AdeleRing (𝓞 F) F) g
  let G := adelicStandardGaussian χ
  let x := τ G - G
  let f := τ x - (2 : ℂ) • x
  let P := adelePolarValues (F := F)
  have h₀ (v : ℬ) : (P (τ v)).1 = (P v).1 := by
    change schwartzBruhatUnitTranslate g v (Multiplicative.ofAdd 0) = v (Multiplicative.ofAdd 0)
    rw [schwartzBruhatUnitTranslate_apply, mul_zero]
  have h₁ (v : ℬ) : (P (τ v)).2 = 2 * (P v).2 := by
    let K := (adelicThetaLinearMap F).ker
    have hact := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 g v
    have hn := globalThetaPolarValues_snd_translate y (K.mkQL v)
    have hu : (P (τ v)).2 = ((ideleClassNorm F y).val : ℝ) * (P v).2 :=
      (congrArg (fun u ↦ (globalThetaPolarValues (F := F) u).2) hact.symm).trans hn
    rw [hy] at hu
    exact hu
  have hsub : f ∈ adelePolarSubspace F := by
    change P f = 0
    have hsa : (P x).1 = 0 := by simp [x, h₀]
    ext <;> simp [f, h₀, h₁, hsa]
  refine ⟨⟨f,hsub⟩, ?_⟩
  let D := (adelicEigendistribution_normalized χ).choose
  let B := fun z ↦ ideleClassNormTwist χ z y
  have hval : (fun z ↦ D z f) = fun z ↦ (B z - 2) * (B z - 1) := by
    funext z
    have hN := ((adelicEigendistribution_normalized χ).choose_spec.2.1 z (D z)).mp rfl
    have hD (v : ℬ) : D z (τ v) = B z * D z v := hN.1 g v
    have hG : D z G = 1 := hN.2
    simp [f, x, hD, hG]
    ring
  change meromorphicOrderAt (fun z ↦ D z f) w = 1
  rw [hval]
  have hB : B = fun z ↦ (χ y : ℂ) * Complex.exp (((Real.log 2 : ℝ) : ℂ) * z) := by
    funext z
    change (χ y : ℂ) * ((((ideleClassNorm F y).val : ℝ) : ℂ) ^ z) = _
    rw [hy]
    change (χ y : ℂ) * ((2 : ℂ) ^ z) = _
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    congr 3
    norm_cast
  have hd : HasDerivAt B ((χ y : ℂ) * (Complex.exp (((Real.log 2 : ℝ) : ℂ) * w) * (Real.log 2 : ℝ))) w := by
    rw [hB]
    exact (((hasDerivAt_id w).const_mul _).cexp.const_mul _).congr_deriv (by simp)
  apply stripTheta_polarFactor_order (B := B) (by rw [hB]; fun_prop) hd
  · exact mul_ne_zero (Circle.coe_ne_zero _) (mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'))
  · rcases he with he | he
    · exact Or.inl (DFunLike.congr_fun he y)
    · refine Or.inr ((DFunLike.congr_fun he y).trans ?_)
      change 1 * ((((ideleClassNorm F y).val : ℝ) : ℂ) ^ (1 : ℂ)) = 2
      rw [hy, Complex.cpow_one, one_mul]
      rfl

/-- Paper: Theorems 3.4.3.3(2), p. 153, and 10.2.2.1, p. 446. At each fixed
point, the minimum vanishing order over all entire polar-free theta Mellin
transforms is the positive part of the completed Hecke divisor there.
Deviation: This pointwise consequence uses the Gaussian-normalized factorization
with its nonzero Tamagawa scalar. It includes both simple poles after cancellation. -/
theorem isLeast_globalThetaMellinIntegral_orders (χ : PontryaginDual C𝔽) (w : ℂ) :
    IsLeast (Set.range fun f : adelePolarSubspace F ↦
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w)
      (max 0 (meromorphicOrderAt (continuedCompletedHeckeL χ) w)) := by
  let Z (f : adelePolarSubspace F) (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  let L := continuedCompletedHeckeL χ
  have hZ (f : adelePolarSubspace F) : 0 ≤ meromorphicOrderAt (Z f) w := by
    obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
    exact (globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ |>.analyticAt w).meromorphicOrderAt_nonneg
  refine ⟨?_, ?_⟩
  · by_cases he : ideleClassNormTwist χ w = 1 ∨
        ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1
    · obtain ⟨f, hf⟩ := stripTheta_exists_normalized_order_one χ w he
      have hp : meromorphicOrderAt L w = -1 := continuedCompletedHeckeL_order_of_exceptional χ w he
      have h := (stripTheta_mellin_factor_order χ f w).2
      refine ⟨f, ?_⟩
      change meromorphicOrderAt (Z f) w = max 0 (meromorphicOrderAt L w)
      exact h.trans (by rw [hf, hp]; decide)
    · obtain ⟨f,hf⟩ := exists_globalThetaMellinIntegral_order_eq_of_regular χ w (not_or.mp he).1 (not_or.mp he).2
      exact ⟨f, hf.trans (max_eq_right (hf ▸ hZ f)).symm⟩
  · rintro _ ⟨f,rfl⟩
    exact max_le (hZ f) (stripTheta_mellin_order χ f w).1

/-- The unweighted Haar integral of a weighted polar-free theta function against an
admitted zero jet vanishes, including the center shift in its multiplicity. -/
private theorem stripTheta_weighted_moment_zero (χ : PontryaginDual C𝔽)
    (f : adelePolarSubspace F) (a b t : ℝ) (k : ℕ)
    (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a + b, t))).untop₀.toNat) :
    ∫ g, modulationWeight m𝔽 a (adelicTheta f.val) g * spectralZeroJet χ b t k g ∂μ𝔽 = 0 := by
  let χq : QuasiCharacter C𝔽 :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hi := globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf'
  have hz : (shift(a + b, t)).re ∈ Ioo (a+b-1) (a+b+1) := by simp
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m𝔽 μ𝔽 χq
    (fun σ _ n ↦ spectralLineJet_functional_moment m𝔽 μ𝔽 χq (adelicTheta f.val) hi σ n) k hz
  have h : (∫ g, modulationWeight m𝔽 a (adelicTheta f.val) g * spectralZeroJet χ b t k g ∂μ𝔽) =
      iteratedDeriv k (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) (shift(a+b,t)) := by
    refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans hderiv.symm
    have hpos : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f.val g *
        (quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(b,t)) g * (logNorm g : ℂ)^k) =
      adelicTheta f.val g * (logNorm g : ℂ)^k *
        quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(a+b,t)) g
    rw [quasiCharacterNormTwist_eq_exp, quasiCharacterNormTwist_eq_exp,
      Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Complex.ofReal_mul]
    have e : Complex.exp ((shift(a+b,t)) * (logNorm g : ℂ)) =
        Complex.exp ((logNorm g : ℂ) * (a : ℂ)) * Complex.exp ((shift(b,t)) * (logNorm g : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    change Complex.exp ((logNorm g : ℂ) * (a : ℂ)) * adelicTheta f.val g *
        (χq g * Complex.exp ((shift(b,t)) * (logNorm g : ℂ)) * (logNorm g : ℂ)^k) =
      adelicTheta f.val g * (logNorm g : ℂ)^k * (χq g * Complex.exp ((shift(a+b,t)) * (logNorm g : ℂ)))
    rw [e]
    ring
  exact h.trans (stripTheta_mellin_zero χ f _ k hk)

/-- Paper: Theorem 10.2.2.1, p. 446. Every strip jet annihilates the closed
weighted polar-free theta image.
Deviation: At a strip endpoint the jet order must be strictly below (s − 1) / 2. -/
theorem spectralStripJet_commonKernel_forward (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (y : W(-α, α, s))
    (hy : y ∈ globalThetaSobolev F a (stripI(hα)) hs) (j : SpectralStripJetIndex χ a α s) :
    spectralSobolevPairing y ((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) = 0 := by
  let u : W'(-α, α, s) := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let Λ := T.symm u
  have hp (v : W(-α, α, s)) : Λ v = spectralSobolevPairing v u :=
    (spectralSobolevPairing_dual (stripI(hα)) hs Λ v).2.trans
      (congrArg (spectralSobolevPairing v) (T.apply_symm_apply u))
  have habs : μ𝔽 ≪ L2μ'(-α, α, s) :=
    withDensity_absolutelyContinuous' (symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g))))
  have hrep : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] stripJet(χ, j) := habs.ae_le (MemLp.coeFn_toLp _)
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
  have hgen (f : adelePolarSubspace F) : Λ (E (Submodule.Quotient.mk f)) = 0 := by
    rw [hp]
    have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose_spec.2 f
    have hN {b : ℝ} (N : ℕ) : spectralStripMultiplicity α s b N ≤ N := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    exact (integral_congr_ae (hE.mul hrep)).trans (stripTheta_weighted_moment_zero
      (χ j.val.1) f a j.val.2.1 j.val.2.2.1 j.val.2.2.2 (j.property.trans_le (hN _)))
  have hR : E.toLinearMap.range ≤ Λ.ker := by
    rintro _ ⟨v, rfl⟩
    induction v using Submodule.Quotient.induction_on with
    | H f => exact hgen f
  exact (hp y).symm.trans ((E.toLinearMap.range.topologicalClosure_minimal hR Λ.isClosed_ker) hy)

/-- Paper: Theorem 10.2.2.1, p. 446. A Sobolev vector whose strip moments vanish
can be approximated in the strip norm by weighted polar-free theta tests.
Deviation: The boundary moments use the strict reciprocal-weight cutoff.
Gap: The finite-band projection argument on p. 443 does not construct these
approximants. The complementary projections only exhaust the span of the jet representers. -/
theorem spectralStripJet_approximation (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
    ∀ y : W(-α, α, s), (∀ j, spectralSobolevPairing y (u j) = 0) → ∀ ε > (0 : ℝ),
      ∃ f : adelePolarSubspace F, ‖y - E (Submodule.Quotient.mk f)‖ < ε := by sorry

end StripThetaAnnihilation

/-- Paper: Theorem 10.2.2.1, p. 446. The weighted theta closure is the common
kernel of all surviving strip evaluations.
Gap: The complementary projections of §9.3 exhaust the orthogonal of the
common kernel. Identifying this kernel with the geometric theta closure
requires a separate approximation in the strip norm. -/
theorem spectralStripJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    JetKernel(a, stripI(hα), hs, u) := by
  intro u y
  refine ⟨spectralStripJet_commonKernel_forward χ hα hs y, fun hy ↦ ?_⟩
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
  change y ∈ closure (E.toLinearMap.range : Set W(-α, α, s))
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  obtain ⟨f, hf⟩ := spectralStripJet_approximation χ _hχ hα hs y hy ε hε
  exact ⟨_, ⟨Submodule.Quotient.mk f, rfl⟩, (dist_eq_norm _ _).trans_lt hf⟩

namespace StripInterpolation

/-- Removing some of a finite-order zero within the entire Schwartz–Bergman space
preserves the orders at every other point. -/
private theorem divide_at_point {f : ℂ → ℂ} (hf : f ∈ schwartzBergmanSubmodule univ)
    (w : ℂ) {n k : ℕ} (horder : analyticOrderAt f w = n) (hk : k ≤ n) :
    ∃ q : ℂ → ℂ, q ∈ schwartzBergmanSubmodule univ ∧ analyticOrderAt q w = k ∧
      ∀ v ≠ w, analyticOrderAt q v = analyticOrderAt f v := by
  classical
  have hd : Differentiable ℂ f := differentiableOn_univ.mp (by simpa using hf.2.1)
  obtain ⟨g, hg, hgw, hnear⟩ := (hd.analyticAt w).analyticOrderAt_eq_natCast.mp horder
  let d := n - k
  have hnk : d + k = n := Nat.sub_add_cancel hk
  let q (z : ℂ) := if z = w then (z - w)^k * g z else f z / (z - w)^d
  have hlocal : q =ᶠ[𝓝 w] fun z ↦ (z - w)^k * g z := by
    filter_upwards [hnear] with z he
    by_cases hz : z = w
    · simp [q, hz]
    · simp only [q, ite_eq_right hz]
      rw [div_eq_iff (pow_ne_zero _ (sub_ne_zero.mpr hz)), he, ← hnk, pow_add]
      simp only [smul_eq_mul]
      ring
  have ha : AnalyticAt ℂ q w :=
    ((analyticAt_id.sub analyticAt_const).pow k |>.mul hg).congr hlocal.symm
  have hother {v : ℂ} (hv : v ≠ w) :
      q =ᶠ[𝓝 v] fun z ↦ f z / (z - w)^d := by
    filter_upwards [eventually_ne_nhds hv] with z hz using ite_eq_right hz
  have hdq : Differentiable ℂ q := by
    intro z
    by_cases hz : z = w
    · simpa [hz] using ha.differentiableAt
    · have hh : DifferentiableAt ℂ (fun u : ℂ ↦ f u / (u - w)^d) z :=
        (hd z).div ((differentiableAt_id.sub_const w).pow d) (pow_ne_zero d (sub_ne_zero.mpr hz))
      exact hh.congr_of_eventuallyEq (hother hz)
  refine ⟨q, ⟨by simp, by simpa using hdq.differentiableOn (s := univ), ?_⟩,
    ha.analyticOrderAt_eq_natCast.mpr ⟨g, hg, hgw, hlocal⟩, ?_⟩
  · intro a b hab hI N
    obtain ⟨B, hB⟩ := hf.2.2 a b hab hI N
    have hc : Continuous (fun z : ℂ ↦ ‖z^N * q z‖) :=
      ((continuous_id.pow N).mul hdq.continuous).norm
    obtain ⟨C, hC⟩ := (isCompact_closedBall w 1).bddAbove_image hc.continuousOn
    refine ⟨max C B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    by_cases hdist : z ∈ Metric.closedBall w 1
    · exact (hC ⟨z, hdist, rfl⟩).trans (le_max_left _ _)
    · have hnorm : 1 < ‖z - w‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hdist
      have hne : z ≠ w := by rintro rfl; norm_num at hnorm
      change ‖z^N * q z‖ ≤ max C B
      rw [show q z = f z / (z - w)^d from ite_eq_right hne, ← mul_div_assoc, norm_div, norm_pow]
      exact (div_le_self (norm_nonneg _) (one_le_pow₀ hnorm.le)).trans
        ((hB ⟨z, hz, rfl⟩).trans (le_max_right _ _))
  · intro v hv
    have hmul : f =ᶠ[𝓝 v] fun z ↦ (z - w)^d * q z := by
      filter_upwards [hother hv, eventually_ne_nhds hv] with z hq hz
      rw [hq]
      field_simp
    have hor : analyticOrderAt (fun z : ℂ ↦ (z - w)^d) v = 0 :=
      (AnalyticAt.analyticOrderAt_eq_zero (by fun_prop)).mpr (pow_ne_zero _ (sub_ne_zero.mpr hv))
    rw [analyticOrderAt_congr hmul, analyticOrderAt_fun_mul (by fun_prop) (hdq.analyticAt v), hor, zero_add]

/-- Gaussian damping converts an entire function bounded on closed vertical substrips
to an entire Schwartz–Bergman function without changing any vanishing orders. -/
private theorem gaussian_of_strip_bound {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hb : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C) :
    (fun z ↦ Complex.exp (z^2) * f z) ∈ schwartzBergmanSubmodule univ ∧
    ∀ z, analyticOrderAt (fun u ↦ Complex.exp (u^2) * f u) z = analyticOrderAt f z := by
  let e (z : ℂ) := Complex.exp (z^2)
  have ha : Differentiable ℂ e := by dsimp [e]; fun_prop
  have he : e ∈ schwartzBergmanSubmodule univ := by
    simpa [e] using gaussian_mem_schwartzBergmanSubmodule univ isOpen_univ
  refine ⟨⟨by simp, (ha.mul hd).differentiableOn, ?_⟩, ?_⟩
  · intro a b hab hI N
    obtain ⟨A, hA⟩ := he.2.2 a b hab hI N
    obtain ⟨C, hC⟩ := hb a b hab
    refine ⟨max A 0 * max C 0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z^N * (e z * f z)‖ ≤ _
    rw [← mul_assoc, norm_mul]
    exact mul_le_mul ((hA ⟨z, hz, rfl⟩).trans (le_max_left _ _))
      ((hC z hz).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  · intro z
    have h0 := (ha.analyticAt z).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
    change analyticOrderAt (fun u ↦ e u * f u) z = _
    rw [analyticOrderAt_fun_mul (ha.analyticAt z) (hd.analyticAt z), h0, zero_add]

/-- A two-sided Laplace integral absolutely convergent at both real endpoints is
bounded uniformly across that closed complex substrip. -/
private theorem laplace_strip_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℂ) (l : X → ℝ) (h : ∀ t : ℝ,
      Integrable (fun x ↦ u x * Complex.exp ((t : ℂ) * (l x : ℂ))) μ) (a b : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖∫ x, u x * Complex.exp (z * (l x : ℂ)) ∂μ‖ ≤ C := by
  let M (r : ℝ) (x : X) := ‖u x * Complex.exp ((r : ℂ) * (l x : ℂ))‖
  refine ⟨∫ x, M a x + M b x ∂μ, fun z hz ↦
    norm_integral_le_of_norm_le ((h a).norm.add (h b).norm) (ae_of_all _ fun x ↦ ?_)⟩
  have he (v : ℂ) : ‖u x * Complex.exp (v * (l x : ℂ))‖ =
      ‖u x‖ * Real.exp (v.re * l x) := by simp [Complex.norm_exp, Complex.mul_re]
  by_cases hxl : 0 ≤ l x
  · apply (le_add_of_nonneg_left (a := M b x) (norm_nonneg _)).trans'
    dsimp only [M]
    rw [he, he, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz.2 hxl)) (norm_nonneg _)
  · apply (le_add_of_nonneg_right (a := M a x) (norm_nonneg _)).trans'
    dsimp only [M]
    rw [he, he, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hz.1 (le_of_not_ge hxl))) (norm_nonneg _)

/-- A triangular collection in a linear subspace interpolates all the coordinates
of one finite jet. -/
private theorem finite_interpolation {n : ℕ} (S : Submodule ℂ (Fin n → ℂ))
    (hpivot : ∀ j : Fin n, ∃ v ∈ S, (∀ i < j, v i = 0) ∧ v j ≠ 0)
    (c : Fin n → ℂ) : c ∈ S := by
  have he (k : ℕ) (hk : k ≤ n) : ∃ v ∈ S, ∀ i : Fin n, (i : ℕ) < k → v i = c i := by
    induction k with
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, hvi⟩ := ih (by omega)
      let j : Fin n := ⟨k, by omega⟩
      obtain ⟨u, hu, hu0, huj⟩ := hpivot j
      let d := (c j - v j) / u j
      refine ⟨v + d • u, S.add_mem hv (S.smul_mem d hu), ?_⟩
      intro i hi
      by_cases hik : (i : ℕ) < k
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu0 i hik, mul_zero, add_zero, hvi i hik]
      · have hij : i = j := Fin.ext (by change (i : ℕ) = k; omega)
        subst i
        change v j + (c j - v j) / u j * u j = c j
        rw [div_mul_cancel₀ _ huj]
        ring
  obtain ⟨v, hv, hvc⟩ := he n le_rfl
  exact (funext fun i ↦ hvc i i.isLt) ▸ hv

/-- Exact order at one zero and the required vanishing at other zeros produce an
entire Schwartz–Bergman transform with arbitrary prescribed finite jet at that point. -/
private theorem interpolate_transform {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hb : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C)
    (w : ℂ) (n : ℕ) (horder : analyticOrderAt f w = n) (c : Fin n → ℂ) :
    ∃ H : schwartzBergmanSubmodule univ,
      (∀ i : Fin n, iteratedDeriv i.val H.val w = c i) ∧
      ∀ v ≠ w, ∀ m : ℕ, (∀ k < m, iteratedDeriv k f v = 0) →
        ∀ k < m, iteratedDeriv k H.val v = 0 := by
  let B := schwartzBergmanSubmodule univ
  have han (H : B) : Differentiable ℂ H.val := differentiableOn_univ.mp (by simpa using H.property.2.1)
  let ev (z : ℂ) (i : ℕ) : B →ₗ[ℂ] ℂ := {
    toFun H := iteratedDeriv i H.val z
    map_add' u v := iteratedDeriv_fun_add ((han u).analyticAt z).contDiffAt ((han v).analyticAt z).contDiffAt
    map_smul' c u := iteratedDeriv_fun_const_smul_field c u.val }
  let index := {p : ℂ × ℕ × ℕ //
    p.1 ≠ w ∧ p.2.2 < p.2.1 ∧ (∀ k < p.2.1, iteratedDeriv k f p.1 = 0)}
  let V : Submodule ℂ B := ⨅ p : index, (ev p.val.1 p.val.2.2).ker
  let A : B →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi fun i ↦ ev w i.val
  have hV (v : B) : v ∈ V ↔ ∀ p : index, iteratedDeriv p.val.2.2 v.val p.val.1 = 0 := by
    simp only [V, Submodule.mem_iInf, LinearMap.mem_ker, ev, LinearMap.coe_mk, AddHom.coe_mk]
  let g (z : ℂ) := Complex.exp (z^2) * f z
  obtain ⟨hg, hgo⟩ := gaussian_of_strip_bound hd hb
  have hs := finite_interpolation (V.map A) (fun (i : Fin n) ↦ ?_) c
  · obtain ⟨H, hH, hc⟩ := hs
    refine ⟨H, fun i ↦ congrFun hc i, fun v hv m hm k hk ↦ ?_⟩
    exact (hV H).mp hH ⟨(v, m, k), hv, hk, hm⟩
  · obtain ⟨q, hq, hw, haway⟩ := divide_at_point (f := g) hg w ((hgo w).trans horder) i.isLt.le
    let Q : B := ⟨q, hq⟩
    have hpivot := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ((han Q).analyticAt w)).mp hw
    refine ⟨A Q, ⟨Q, (hV Q).mpr ?_, rfl⟩, fun j hj ↦ hpivot.1 j hj, hpivot.2⟩
    intro ⟨⟨v, m, k⟩, hv, hk, hm⟩
    have ho := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hd.analyticAt v)).mpr hm
    rw [← hgo v, ← haway v hv] at ho
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((han Q).analyticAt v)).mp ho k hk
/-- Starting from a biorthogonal family, the other biorthogonal families are
exactly its translations by one common-kernel vector per index. -/
private theorem density_iff {J E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : J → E →ₗ[ℂ] ℂ) (D : (J → E) → Prop) (v : J → E)
    (hv : ∀ i, L i (v i) = 1) (hz : ∀ i j, i ≠ j → L j (v i) = 0) :
    (∃ y : J → E, (∀ i, L i (y i) = 1) ∧
        (∀ i j, i ≠ j → L j (y i) = 0) ∧ D y) ↔
      ∃ r : J → E, (∀ i j, L j (r i) = 0) ∧ D (fun i ↦ v i + r i) := by
  constructor
  · rintro ⟨y, hone, hzero, hy⟩
    refine ⟨fun i ↦ y i - v i, fun i j ↦ ?_, ?_⟩
    · rw [map_sub]
      by_cases e : i = j
      · subst j
        simp [hone, hv]
      · simp [hzero i j e, hz i j e]
    · have he (i : J) : v i + (y i - v i) = y i := by abel
      simpa only [he] using hy
  · rintro ⟨r, hr, hy⟩
    refine ⟨fun i ↦ v i + r i, fun i ↦ ?_, fun i j hij ↦ ?_, hy⟩
    · simp [hv, hr]
    · simp [hz i j hij, hr]

end StripInterpolation

section StripProfileInterpolation

/-- An integral supported on a nontrivial compact character vanishes by Haar invariance. -/
private theorem stripProfile_orthogonality {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [MeasurableMul₂ G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (χ η : PontryaginDual G) (g : G) (hg : χ g ≠ η g)
    (q : G → ℂ) (hq : ∀ x, q (g * x) = q x) :
    (∫ x, ((χ x : ℂ)⁻¹ * (η x : ℂ)) * q x ∂μ) = 0 := by
  let v (x : G) := (χ x : ℂ)⁻¹ * (η x : ℂ)
  have hmul (x : G) : v (g * x) = v g * v x := by
    dsimp [v]
    rw [map_mul, map_mul, Circle.coe_mul, Circle.coe_mul, mul_inv_rev]
    ring
  have hne : v g ≠ 1 := by
    intro he
    apply hg
    apply Subtype.ext
    exact (inv_mul_eq_one₀ (Circle.coe_ne_zero _)).mp he
  let A := ∫ x, v x * q x ∂μ
  have h : A = v g * A :=
    (integral_mul_left_eq_self (μ := μ) (fun x ↦ v x * q x) g).symm.trans <| by
      rw [← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      change v (g * x) * q (g * x) = v g * (v x * q x)
      rw [hmul, hq, mul_assoc]
  change A = 0
  exact (mul_eq_zero.mp (by linear_combination -h : (v g - 1) * A = 0)).resolve_left (sub_ne_zero.mpr hne)

/-- The physical strip jet is the chosen compact character times an exponential polynomial. -/
private theorem stripProfile_jet (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (x : C𝔽) :
    spectralZeroJet χ b t k x = (χ x : ℂ) * Complex.exp (shift(b, t) * (logNorm x : ℂ)) *
      (logNorm x : ℂ)^k := by
  let η : QuasiCharacter C𝔽 := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  exact congrArg (fun u : ℂ ↦ u * (logNorm x : ℂ)^k) (quasiCharacterNormTwist_eq_exp m𝔽 η _ _)

/-- Pullback from weighted radial L² with the inverse base character. -/
private theorem stripTail_radial_lift (ψ : PontryaginDual C𝔽) {α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s) :
    ∃ L : CompactIntervalSobolev volume id (-α) α s →L[ℂ] W(-α, α, s), ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽]
      fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x) := by
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let E := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 (-α) α s
  let R := sobolev_character_pull m𝔽 hm𝔽 hms𝔽 _ (continuous_intervalSobolevDensity' (-α) α s)
    (intervalSobolevDensity_pos (-α) α s) (fun x ↦ (ψ⁻¹ x : ℂ)) (continuous_subtype_val.comp ψ⁻¹.continuous)
    (fun _ ↦ Circle.norm_coe _)
  let L := E.choose.symm.toContinuousLinearMap.comp R.choose
  refine ⟨L, fun f ↦ (E.choose_spec (L f)).1.symm.trans ?_⟩
  rw [show E.choose (L f) = R.choose f from E.choose.apply_symm_apply _]
  apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
  refine (R.choose_spec f).trans (.of_forall fun x ↦ ?_)
  change (((ψ x)⁻¹ : Circle) : ℂ) * f (logNorm x) = (ψ x : ℂ)⁻¹ * f (logNorm x)
  rw [Circle.coe_inv]

/-- Every scalar two-sided exponential-decay profile lifts to the ambient strip
Sobolev space in the inverse base-character component. -/
private theorem stripProfile_sobolev (χ : PontryaginDual C𝔽) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (p : PositiveRealExponentialDecay univ) :
    ∃ y : W(-α, α, s), (y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * p.val (logNorm x) := by
  obtain ⟨L, hL⟩ := stripTail_radial_lift χ hα hs
  let P := scalarIntervalSobolev_dense (-α) α s (stripI(hα)) hs univ isOpen_univ
    ordConnected_univ (subset_univ _)
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  refine ⟨L (P.choose p), (hL _).trans ?_⟩
  apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
  have he := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp (P.choose_spec.2.2 p)
  filter_upwards [he] with x hx using congrArg ((χ x : ℂ)⁻¹ * ·) hx

/-- Finite order strip moments of inverse profiles on a wider open interval. -/
private theorem stripProfile_log_moment {I : Set ℝ} (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hl : MeasurePreserving logNorm ν volume)
    (p : PositiveRealExponentialDecay I) (k : ℕ) (z : ℂ) (hz : z.re ∈ I) :
    (∫ x : C𝔽, (((logNorm x : ℂ)^k) * p.val (logNorm x)) * Complex.exp (z * (logNorm x : ℂ)) ∂μ𝔽) =
      ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ) *
        iteratedDeriv k (mellin (fun t ↦ p.val (Real.log t))) z := by
  rw [scalarDecay_mellin_deriv hI p k hz, mellin_logProfile (fun t : ℝ ↦ (t : ℂ)^k * p.val t)]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  have hp : Continuous p.val := by
    refine (logExponentialDecayTwist I ⟨0, h0⟩ p).continuous.congr fun t ↦ ?_
    simpa using logExponentialDecayTwist_apply I ⟨0, h0⟩ p t
  let q (t : ℝ) := (t : ℂ)^k * p.val t * Complex.exp (z * (t : ℂ))
  have hq : Continuous q := ((Complex.continuous_ofReal.pow k).mul hp).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  exact (integral_map hl.measurable.aemeasurable (f := q) hq.aestronglyMeasurable).symm.trans
    (congrArg (fun η : Measure ℝ ↦ ∫ t, q t ∂η) hl.map_eq)

end StripProfileInterpolation

/-- Paper: Theorem 10.2.2.1, p. 446. The discrete divisor in each norm
chart gives countably many strip jets over the countable norm-one dual. -/
theorem spectralStripJet_countable (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a α s : ℝ) :
    Countable (SpectralStripJetIndex χ a α s) := by
  have hK : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let Z (ω : PontryaginDual C₁) := {z : ℂ | 0 < multiplicity(χ ω, z)}
  have hc (ω : PontryaginDual C₁) : (Z ω).Countable := by
    have hm := (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn
    have hcod : (Z ω)ᶜ ∈ Filter.codiscrete ℂ := by
      filter_upwards [hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
      rcases hz.2 with h | h <;> simp [Z, h]
    let : DiscreteTopology (Z ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hcod).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let W := ⋃ ω, Z ω
  let : Countable W := (Set.countable_iUnion hc).to_subtype
  have hz (j : SpectralStripJetIndex χ a α s) : shift(a + j.val.2.1, j.val.2.2.1) ∈ W := by
    apply Set.mem_iUnion.mpr
    refine ⟨j.val.1, ?_⟩
    have h := j.property
    change 0 < multiplicity(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1))
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
    split_ifs at h <;> omega
  let e (j : SpectralStripJetIndex χ a α s) : PontryaginDual C₁ × W × ℕ :=
    (j.val.1, ⟨shift(a + j.val.2.1, j.val.2.2.1), hz j⟩, j.val.2.2.2)
  apply Function.Injective.countable (f := e)
  intro i j hij
  have hre := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.re) hij
  have him := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.im) hij
  have hω := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.1) hij
  have hk := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.2) hij
  exact Subtype.ext (Prod.ext hω (Prod.ext (by simpa [e] using hre) (Prod.ext (by simpa [e] using him) hk)))

namespace StripMultiplier

/-- Pointwise convergence to zero under an L² envelope gives convergence in L². -/
private theorem l2_dominated {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι}
    [l.IsCountablyGenerated] (u : ι → X → ℂ) (hu : ∀ n, MemLp (u n) 2 μ)
    (f : X → ℂ) (hf : MemLp f 2 μ) (hbound : ∀ n x, ‖u n x‖ ≤ 2 * ‖f x‖)
    (hlim : ∀ x, Tendsto (fun n ↦ u n x) l (𝓝 0)) :
    Tendsto (fun n ↦ (eLpNorm (u n) 2 μ).toReal) l (𝓝 0) := by
  let D (n : ι) (x : X) := ‖u n x‖ ^ 2
  have h : Tendsto (fun n ↦ ∫ x, D n x ∂μ) l (𝓝 (∫ _ : X, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ 4 * ‖f x‖ ^ 2)
    · exact .of_forall fun n ↦ (hu n).aestronglyMeasurable.norm.pow 2
    · refine .of_forall fun n ↦ .of_forall fun x ↦ ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (2 * ‖f x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound n x) _
        _ = _ := by ring
    · exact hf.norm.integrable_sq.const_mul 4
    · exact .of_forall fun x ↦ by simpa [D] using (hlim x).norm.pow 2
  have hs (n : ι) : ‖(hu n).toLp _‖ ^ 2 = ∫ x, D n x ∂μ := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    exact integral_congr_ae ((hu n).coeFn_toLp.fun_comp fun t ↦ ‖t‖ ^ 2)
  simpa only [integral_zero, comp_def, ← hs, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    Lp.norm_toLp, Real.sqrt_sq ENNReal.toReal_nonneg] using (Real.continuous_sqrt.tendsto _).comp h

/-- A bounded holomorphic multiplier preserves the entire family of substrip
bounds in the Schwartz–Bergman space. -/
private theorem multiply_mem {I : Set ℝ} (H : SchwartzBergman I) (b : ℂ → ℂ)
    (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I)) (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1) :
    (fun z ↦ b z * H.val z) ∈ schwartzBergmanSubmodule I := by
  refine ⟨fun z hz ↦ ?_, hb.mul H.property.2.1, ?_⟩
  · exact (congrArg (b z * ·) (H.property.1 hz)).trans (mul_zero _)
  · intro a c hac hsub k
    obtain ⟨M, hM⟩ := H.property.2.2 a c hac hsub k
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ k * (b z * H.val z)‖ ≤ M
    rw [mul_left_comm, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc z (hsub hz))).trans (hM ⟨z, hz, rfl⟩)

/-- Multiplication by bounded, pointwise convergent analytic multipliers converges
in the full Schwartz–Bergman topology on the open strip. -/
private theorem tendsto_multiply {I : Set ℝ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (H : SchwartzBergman I) (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    let G (n : ι) : SchwartzBergman I := ⟨_, multiply_mem H (b n) (hb n) (hc n)⟩
    Tendsto G l (𝓝 H) := by
  intro G
  let P (i : I × ℕ) : Seminorm ℂ (schwartzBergmanSubmodule I) :=
    Seminorm.of (fun f ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  apply ((withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P).tendsto_nhds G H).mpr
  rintro ⟨a, k⟩ ε hε
  let z (t : ℝ) := (a.val : ℂ) + t * Complex.I
  have hz (t : ℝ) : (z t).re ∈ I := by simp [z]
  let F := weightedVerticalTrace a k H.val
  let U (n : ι) := weightedVerticalTrace a k (G n - H).val
  have hU (n : ι) (t : ℝ) : U n t = (b n (z t) - 1) * F t := by
    change (z t)^k * (b n (z t) * H.val (z t) - H.val (z t)) = (b n (z t) - 1) * ((z t)^k * H.val (z t))
    ring
  have hB (n : ι) (t : ℝ) : ‖U n t‖ ≤ 2 * ‖F t‖ := by
    rw [hU, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖b n (z t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith [hc n (z t) (hz t)]
  have ht (t : ℝ) : Tendsto (fun n ↦ U n t) l (𝓝 0) := by
    simp only [hU]
    simpa using ((hl (z t) (hz t)).sub_const (1 : ℂ)).mul_const (F t)
  have hx := l2_dominated U (fun n ↦ schwartzBergman_trace_memLp I a 2 (by norm_num)
    (by norm_num) k (G n - H)) F (schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) k H) hB ht
  exact hx.eventually (gt_mem_nhds hε)

/-- Inverse Fourier–Mellin transform transports bounded cutoff convergence to the
exponential test topology, hence to the norm on every enclosed Sobolev interval. -/
private theorem scalar_approximation {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) (p : PositiveRealExponentialDecay I) :
    ∃ q : ι → PositiveRealExponentialDecay I, Tendsto q l (𝓝 p) ∧
      ∀ n, EqOn (mellin (fun t ↦ (q n).val (Real.log t)))
        (fun z ↦ b n z * mellin (fun t ↦ p.val (Real.log t)) z) (Complex.re ⁻¹' I) := by
  let M := positiveRealFourierMellin I hI hInt hne
  let H := M p
  let G (n : ι) : SchwartzBergman I := ⟨_, multiply_mem H (b n) (hb n) (hc n)⟩
  let q (n : ι) := M.symm (G n)
  refine ⟨q, ?_, fun n z hz ↦ ?_⟩
  · have hG : Tendsto G l (𝓝 H) := tendsto_multiply H b hb hc hl
    have hq : Tendsto q l (𝓝 (M.symm H)) := (M.symm.continuous.tendsto H).comp hG
    exact (M.symm_apply_apply p) ▸ hq
  · have hn := positiveRealFourierMellin_apply I hI hInt hne (q n) z hz
    have hp := positiveRealFourierMellin_apply I hI hInt hne p z hz
    calc
      _ = (M (q n)).val z := hn.symm
      _ = (G n).val z := congrArg (fun A : SchwartzBergman I ↦ A.val z) (M.apply_symm_apply _)
      _ = _ := congrArg (b n z * ·) hp

/-- If the cutoff has the prescribed zero multiplicity, every lower moment of the
cutoff profile vanishes. -/
private theorem lower_jet_zero {I : Set ℝ} (hI : IsOpen I) (p q : PositiveRealExponentialDecay I)
    (b : ℂ → ℂ) (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I))
    (he : EqOn (mellin (fun t ↦ q.val (Real.log t)))
      (fun z ↦ b z * mellin (fun t ↦ p.val (Real.log t)) z) (Complex.re ⁻¹' I))
    (hInt : OrdConnected I) (z : ℂ) (hz : z.re ∈ I) {m k : ℕ}
    (hm : (m : ℕ∞) ≤ analyticOrderAt b z) (hk : k < m) :
    iteratedDeriv k (mellin (fun t ↦ q.val (Real.log t))) z = 0 := by
  let M := positiveRealFourierMellin I hI hInt ⟨z.re, hz⟩
  let H := M p
  have hopen := hI.preimage Complex.continuous_re
  have had : AnalyticAt ℂ b z := hb.analyticAt (hopen.mem_nhds hz)
  have Hanalytic : AnalyticAt ℂ H.val z := H.property.2.1.analyticAt (hopen.mem_nhds hz)
  have hnear : mellin (fun t ↦ q.val (Real.log t)) =ᶠ[𝓝 z] fun w ↦ b w * H.val w := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact (he hw).trans (congrArg (b w * ·) (positiveRealFourierMellin_apply I hI hInt _ p w hw).symm)
  rw [hnear.iteratedDeriv_eq]
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (had.mul Hanalytic)).mp _ k hk
  change (m : ℕ∞) ≤ analyticOrderAt (fun w ↦ b w * H.val w) z
  rw [analyticOrderAt_fun_mul had Hanalytic]
  exact le_trans hm (le_self_add)

end StripMultiplier

section StripSingleJets
open scoped Classical
local notation "Jχ(" χ ", " a ", " α ", " s ")" => SpectralStripJetIndex χ a α s
local notation "Zj(" i ")" => shift((i).val.2.1, (i).val.2.2.1)
local notation "dj(" i ")" => (i).val.2.2.2

/-- The Mellin transform of a polar-free generator is uniformly bounded on each
closed vertical substrip, including after a translation of the center. -/
private theorem stripProfile_theta_strip_bound (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (a : ℝ) :
    let Z := fun z : ℂ ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a : ℂ) + z))
    Differentiable ℂ Z ∧ ∀ l r : ℝ, l ≤ r → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc l r → ‖Z z‖ ≤ C := by
  intro Z
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hd := globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ
  refine ⟨hd.comp (show Differentiable ℂ (fun z : ℂ ↦ (a : ℂ) + z) by fun_prop), ?_⟩
  let u (x : C𝔽) := adelicTheta f.val x * (χ x : ℂ)
  let η : QuasiCharacter C𝔽 := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have he (v : ℂ) (x : C𝔽) : adelicTheta f.val x * ideleClassNormTwist χ v x =
      u x * Complex.exp (v * (logNorm x : ℂ)) := by
    have hh := quasiCharacterNormTwist_eq_exp m𝔽 η v x
    change ideleClassNormTwist χ v x = (χ x : ℂ) * Complex.exp (v * (logNorm x : ℂ)) at hh
    rw [hh, ← mul_assoc]
  have hu (r : ℝ) : Integrable (fun x ↦ u x * Complex.exp ((r : ℂ) * (logNorm x : ℂ))) μ𝔽 :=
    (globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf' _).congr (.of_forall (he r))
  intro l r _
  obtain ⟨C, hC⟩ := StripInterpolation.laplace_strip_bound μ𝔽 u logNorm hu (a + l) (a + r)
  refine ⟨C, fun z hz ↦ ?_⟩
  have hz' : ((a : ℂ) + z).re ∈ Icc (a + l) (a + r) := by
    change a + l ≤ a + z.re ∧ a + z.re ≤ a + r
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hv : Z z = ∫ x, u x * Complex.exp (((a : ℂ) + z) * (logNorm x : ℂ)) ∂μ𝔽 :=
    integral_congr_ae (.of_forall (he _))
  rw [hv]
  exact hC _ hz'

/-- On one compact-character chart every admitted jet has a Schwartz–Bergman
interpolant, vanishing at every remaining admitted jet on that entire chart. -/
private theorem stripProfile_single_chart (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (i : Jχ(χ, a, α, s)) (d : ℂ) :
    ∃ H : SchwartzBergman univ, ∀ j : Jχ(χ, a, α, s), j.val.1 = i.val.1 →
      iteratedDeriv dj(j) H.val Zj(j) = if j = i then d else 0 := by
  classical
  let n (j : Jχ(χ, a, α, s)) := multiplicity(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1))
  have hn (j : Jχ(χ, a, α, s)) : dj(j) < n j := by
    have hj := j.property
    change dj(j) < spectralStripMultiplicity α s j.val.2.1 (n j) at hj
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at hj
    split_ifs at hj <;> omega
  obtain ⟨f, hvan, hnon⟩ := i.exists_thetaMellin_first_nonvanishing
  let Z (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist (χ i.val.1) z)
  let W (z : ℂ) := Z ((a : ℂ) + z)
  have hv (j : Jχ(χ, a, α, s)) : (a : ℂ) + Zj(j) = shift(a + j.val.2.1, j.val.2.2.1) := by
    push_cast
    ring
  have ht (k : ℕ) (j : Jχ(χ, a, α, s)) :
      iteratedDeriv k W Zj(j) = iteratedDeriv k Z (shift(a + j.val.2.1, j.val.2.2.1)) := by
    exact (congrFun (iteratedDeriv_comp_const_add k Z (a : ℂ)) _).trans (congrArg (iteratedDeriv k Z) (hv j))
  obtain ⟨hd, hb⟩ := stripProfile_theta_strip_bound (χ i.val.1) f a
  have ho : analyticOrderAt W Zj(i) = n i := by
    apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hd.analyticAt _)).mpr
    exact ⟨fun k hk ↦ (ht k i).trans (hvan k hk), (ht _ i).trans_ne hnon⟩
  let c (k : Fin (n i)) := if (k : ℕ) = dj(i) then d else 0
  obtain ⟨H, hH, hother⟩ := StripInterpolation.interpolate_transform hd hb Zj(i) (n i) ho c
  refine ⟨H, fun j hω ↦ ?_⟩
  by_cases he : Zj(j) = Zj(i)
  · have hbj : j.val.2.1 = i.val.2.1 := by simpa using congrArg Complex.re he
    have htj : j.val.2.2.1 = i.val.2.2.1 := by simpa using congrArg Complex.im he
    have hnj : n j = n i := by simp only [n, hω, hbj, htj]
    have hij : j = i ↔ dj(j) = dj(i) :=
      ⟨fun e ↦ congrArg (fun x : Jχ(χ, a, α, s) ↦ dj(x)) e,
        fun h ↦ Subtype.ext (Prod.ext hω (Prod.ext hbj (Prod.ext htj h)))⟩
    rw [he]
    apply (hH ⟨dj(j), (hn j).trans_eq hnj⟩).trans
    by_cases e : j = i
    · simp [c, e]
    · simp [c, e, (not_congr hij).mp e]
  · rw [ite_eq_right (show j ≠ i from fun hj ↦ he (congrArg (fun x : Jχ(χ, a, α, s) ↦ Zj(x)) hj))]
    apply hother Zj(j) he (n j) _ dj(j) (hn j)
    intro k hk
    rw [ht k j]
    apply stripTheta_mellin_zero
    simpa only [n, hω] using hk

local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "finiteJetMoments(" χ ", " a ", " hα ", " hs ")" =>
  {y : W(-_, _, _) | (Function.support (fun j : Jχ(χ, a, _, _) ↦
    spectralSobolevPairing y ((stripU(χ, hα, hs)) j))).Finite}

/-- Every physical moment on the same chart is a scalar Mellin derivative. All
other compact characters have zero pairing. -/
private theorem stripTail_profile_pairing
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {I : Set ℝ} (hI : IsOpen I) (hsub : Icc (-α) α ⊆ I)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hlog : MeasurePreserving logNorm ν volume)
    (p : PositiveRealExponentialDecay I) (y : W(-α, α, s))
    (hy : (y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * p.val (logNorm x)) (j : Jχ(χ, a, α, s)) :
    spectralSobolevPairing y ((stripU(χ, hα, hs)) j) = if j.val.1 = ω then
      ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ) *
        iteratedDeriv dj(j) (mellin (fun t ↦ p.val (Real.log t))) Zj(j) else 0 := by
  have habs : μ𝔽 ≪ L2μ'(-α, α, s) :=
    withDensity_absolutelyContinuous'
      (symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr
        (inv_pos.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g))))
  let q (r : ℝ) := ((r : ℂ)^dj(j) * p.val r) * Complex.exp (Zj(j) * (r : ℂ))
  have hu : (((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) : C𝔽 → ℂ) =ᵐ[μ𝔽] stripJet(χ, j) :=
    habs.ae_le (MemLp.coeFn_toLp _)
  let v (x : C𝔽) := (χ ω x : ℂ)⁻¹ * (χ j.val.1 x : ℂ)
  have hpair : spectralSobolevPairing y ((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) =
      ∫ x, v x * q (logNorm x) ∂μ𝔽 := by
    refine (integral_congr_ae (hy.mul hu)).trans (integral_congr_ae (.of_forall fun x ↦ ?_))
    change ((χ ω x : ℂ)⁻¹ * p.val (logNorm x)) * stripJet(χ, j) x = v x * q (logNorm x)
    rw [stripProfile_jet]
    dsimp only [v, q]
    ring
  rw [hpair]
  by_cases hω : j.val.1 = ω
  · rw [ite_eq_left hω]
    have hv (x : C𝔽) : v x = 1 := by dsimp [v]; rw [hω, inv_mul_cancel₀ (Circle.coe_ne_zero _)]
    simp_rw [hv, one_mul]
    have hz : Zj(j).re ∈ I := by simpa using hsub (j.mem_strip_order_pos hα).1
    exact stripProfile_log_moment hI (hsub ⟨neg_nonpos.mpr hα, hα⟩) ν
      hlog p dj(j) Zj(j) hz
  · rw [ite_eq_right hω]
    have hk : ∃ k : C₁, χ ω k.val ≠ χ j.val.1 k.val := by
      by_contra! he
      apply hω
      rw [← hχ j.val.1, ← hχ ω]
      exact DFunLike.ext _ _ fun k ↦ (he k).symm
    obtain ⟨k, hk⟩ := hk
    apply stripProfile_orthogonality μ𝔽 (χ ω) (χ j.val.1) k.val hk (fun x ↦ q (logNorm x))
    intro x
    change q (Real.log ((ideleClassNorm F (k.val * x)).val : ℝ)) = q (logNorm x)
    rw [map_mul, k.property, one_mul]

/-- Paper: Theorem 10.2.2.1, p. 446. Each admitted strip jet has an ambient Sobolev
interpolant with all its other admitted moments zero.
Deviation: The proof divides a polar-free entire Mellin transform within the scalar
Schwartz–Bergman space and uses the strict Sobolev cutoff at the boundary. -/
theorem spectralStripJet_singleInterpolant (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (i : Jχ(χ, a, α, s)) :
    ∃ y : W(-α, α, s), ∀ j : Jχ(χ, a, α, s),
      spectralSobolevPairing y ((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) =
        if j = i then 1 else 0 := by
  classical
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let c : ℝ := Measure.haarScalarFactor μ𝔽 ν
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
    have hpos : 0 < c := by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν
    exact hpos.ne')
  obtain ⟨H, hH⟩ := stripProfile_single_chart χ i (c : ℂ)⁻¹
  let M := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  let p := M.symm H
  have hM : mellin (fun t ↦ p.val (Real.log t)) = H.val := by
    funext z
    exact (positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty p z
      (mem_univ _)).symm.trans (congrArg (fun u : SchwartzBergman univ ↦ u.val z) (M.apply_symm_apply H))
  obtain ⟨y, hy⟩ := stripProfile_sobolev (χ i.val.1) hα hs p
  refine ⟨y, fun j ↦ ?_⟩
  rw [stripTail_profile_pairing χ hχ i.val.1 hα hs isOpen_univ (subset_univ _)
    ν (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽) p y hy j]
  by_cases hω : j.val.1 = i.val.1
  · rw [ite_eq_left hω, hM, hH j hω]
    split_ifs <;> simp [c, hc]
  · have hj : j ≠ i := fun he ↦ hω (congrArg (fun u : Jχ(χ, a, α, s) ↦ u.val.1) he)
    rw [ite_eq_right hω, ite_eq_right hj]

section StripBlaschkeMultipliers

open Complex MeromorphicOn Metric Real
open scoped ComplexConjugate

private theorem positiveOrder_le_of_finite {u v : WithTop ℤ} (hv : v ≠ ⊤) (h : max 0 u ≤ v) :
    (u.untop₀.toNat : ℤ) ≤ v.untop₀ := by
  cases v with
  | top => contradiction
  | coe n =>
    cases u with
    | top => simp at h
    | coe m =>
      have hm : m ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) h)
      have hn : (0 : ℤ) ≤ n := by exact_mod_cast (le_trans (le_max_left _ _) h)
      simp only [WithTop.untop₀_coe]
      omega

private theorem continuedCompletedHeckeL_order_at_two_nonpos (χ : PontryaginDual C𝔽) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) (2 : ℂ) ≤ 0 := by
  by_contra! h
  have hbad := completedHeckeL_continuation_zeros χ _ (continuedCompletedHeckeL_spec χ).1
    (continuedCompletedHeckeL_spec χ).2 (by norm_num : 0 < (2:ℂ).re) h
  norm_num at hbad

/-- The positive Hecke divisor in every vertical strip centered at real part 2
satisfies the Blaschke condition after conformal transport to the disk.
The test attaining the polar-free divisor minimum at the center is nonzero there. -/
private theorem continuedCompletedHeckeL_strip_blaschke (χ : PontryaginDual C𝔽) {k : ℝ} (hk : 0 < k) :
    Summable (fun w : {w : ℂ // |w.re - 2| < (π / 2) / k} ↦
      ((meromorphicOrderAt (continuedCompletedHeckeL χ) w.val).untop₀.toNat : ℝ) *
        (1 - ‖stripBlaschkeToDisk 2 k w‖)) := by
  let L := continuedCompletedHeckeL χ
  have h₂ : meromorphicOrderAt L (2 : ℂ) ≤ 0 := continuedCompletedHeckeL_order_at_two_nonpos χ
  obtain ⟨f, hf⟩ := (isLeast_globalThetaMellinIntegral_orders χ (2 : ℂ)).1
  let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  have hG₂ : meromorphicOrderAt G 2 = 0 := hf.trans (max_eq_left h₂)
  obtain ⟨h₀,h₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hG : Differentiable ℂ G := globalThetaMellinIntegral_entire_of_vanishing f.val h₀ h₁ χ
  have hzero : G 2 ≠ 0 := (hG.analyticAt _).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hG₂
  let a := (π / 2) / k
  have ha : 0 < a := div_pos (by positivity) hk
  obtain ⟨M, hM⟩ := (stripProfile_theta_strip_bound χ f 0).2 (2-a) (2+a) (by linarith)
  have hB (w : ℂ) (hw : |w.re - (2 : ℂ).re| < (π / 2) / k) : ‖G w‖ ≤ M := by
    have hw' : |w.re - 2| < a := by simpa [a] using hw
    have hwI : w.re ∈ Icc (2-a) (2+a) :=
      ⟨by linarith [(abs_lt.mp hw').1], by linarith [(abs_lt.mp hw').2]⟩
    simpa only [Complex.ofReal_zero, zero_add] using hM w hwI
  have hall := verticalStrip_divisor_blaschke (w₀ := 2) hk G (fun z _ ↦ hG.analyticAt z) hzero hB
  have hGmero : MeromorphicOn G univ := fun z _ ↦ (hG.analyticAt z).meromorphicAt
  have hGfin (w : ℂ) : meromorphicOrderAt G w ≠ ⊤ :=
    MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hGmero
      isPreconnected_univ (x := (2:ℂ)) (mem_univ _) (mem_univ w) (by simp [hG₂])
  let W := {w : ℂ // |w.re-2| < a}
  have hd (w : W) : 0 ≤ 1 - ‖stripBlaschkeToDisk 2 k w‖ := by
    have hx : |w.val.re - (2 : ℂ).re| < (π / 2) / k := by simpa [a] using w.property
    have hh := stripBlaschkeToDisk_mem hk hx
    exact sub_nonneg.mpr (show ‖stripBlaschkeToDisk 2 k w‖ < 1 by simpa [mem_ball] using hh).le
  apply Summable.of_nonneg_of_le (fun w ↦ mul_nonneg (Nat.cast_nonneg _) (hd w)) _ hall
  intro w
  refine mul_le_mul_of_nonneg_right ?_ (hd w)
  exact_mod_cast positiveOrder_le_of_finite (hGfin w)
    ((isLeast_globalThetaMellinIntegral_orders χ (w : ℂ)).2 ⟨f,rfl⟩)

/-- An arbitrary family of distinct Hecke zeros inside the outer strip gives
nonzero pairwise-distinct disk points and the summable multiplicity bound used
by the infinite Blaschke tail products. -/
private theorem continuedCompletedHeckeL_blaschke_family {ι : Type*} (χ : PontryaginDual C𝔽)
    {k : ℝ} (hk : 0 < k) (p : ι → ℂ) (hp : Injective p)
    (hW : ∀ i, |(p i).re - 2| < (π / 2) / k)
    (hZ : ∀ i, 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (p i))
    (m : ι → ℕ) (hm : ∀ i, m i ≤ (meromorphicOrderAt (continuedCompletedHeckeL χ) (p i)).untop₀.toNat) :
    let z (i : ι) := stripBlaschkeToDisk 2 k (p i)
    Injective z ∧ (∀ i, z i ≠ 0) ∧ (∀ i, ‖z i‖ < 1) ∧
      Summable (fun i ↦ (m i : ℝ) * (1 - ‖z i‖)) := by
  intro z
  have hW' (i) : |(p i).re - (2 : ℂ).re| < (π / 2) / k := by simpa using hW i
  have hleft (i) : stripBlaschkeFromDisk 2 k (z i) = p i := stripBlaschkeFromDisk_toDisk hk (hW' i)
  have hnorm (i) : ‖z i‖ < 1 := by simpa [z, mem_ball] using stripBlaschkeToDisk_mem hk (hW' i)
  refine ⟨fun i j h ↦ hp ((hleft i).symm.trans ((congrArg (stripBlaschkeFromDisk 2 k) h).trans (hleft j))),
    fun i h ↦ ?_, hnorm, ?_⟩
  · have he : p i = 2 := (hleft i).symm.trans (by simp [h,stripBlaschkeFromDisk])
    exact (not_lt_of_ge (continuedCompletedHeckeL_order_at_two_nonpos χ)) (he ▸ hZ i)
  · let P (i : ι) : {w : ℂ // |w.re-2| < (π / 2) / k} := ⟨p i, hW i⟩
    have hinj : Injective P := fun x y h ↦ hp (congrArg Subtype.val h)
    have hs := (continuedCompletedHeckeL_strip_blaschke χ hk).comp_injective hinj
    apply Summable.of_nonneg_of_le (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hnorm i).le)) _ hs
    intro i
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hm i)) (sub_nonneg.mpr (hnorm i).le)

/-- On a neighborhood of a prescribed closed Hecke strip, contractive
analytic multipliers tend to one. Each multiplier has the full prescribed
zero orders away from a finite set of distinct points in that closed strip. -/
private theorem exists_hecke_strip_tail_multipliers {ι : Type*} (χ : PontryaginDual C𝔽)
    (a α : ℝ) (hα : 0 ≤ α) (p : ι → ℂ) (hp : Injective p)
    (hstrip : ∀ i, |(p i).re| ≤ α)
    (hz : ∀ i, 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + p i))
    (m : ι → ℕ) (hm : ∀ i, m i ≤ (meromorphicOrderAt (continuedCompletedHeckeL χ)
      ((a : ℂ) + p i)).untop₀.toNat) :
    ∃ B : Finset ι → ℂ → ℂ,
      (∀ S, AnalyticOnNhd ℂ (B S) {w | |w.re| < α+1}) ∧
      (∀ S w, |w.re| < α+1 → ‖B S w‖ ≤ 1) ∧
      (∀ w, |w.re| < α+1 → Tendsto (fun S ↦ B S w) atTop (𝓝 1)) ∧
      ∀ (S : Finset ι) i, i ∉ S → (m i : ℕ∞) ≤ analyticOrderAt (B S) (p i) := by
  let R := |a-2|+α+2
  have hR : 0 < R := by dsimp [R]; linarith [abs_nonneg (a-2)]
  let k := (Real.pi / 2) / R
  have hk : 0 < k := div_pos (by positivity) hR
  have hwidth : (Real.pi / 2) / k = R := by
    dsimp [k]
    field_simp [Real.pi_ne_zero]
  let A (w : ℂ) := (a : ℂ) + w
  have hwide (z : ℂ) (hz' : |z.re| < α+1) : |(A z).re - 2| < (Real.pi/2)/k := by
    rw [hwidth]
    change |((a : ℂ) + z).re - 2| < |a-2| + α + 2
    rw [Complex.add_re, Complex.ofReal_re, show a + z.re - 2 = (a-2) + z.re by ring]
    linarith [abs_add_le (a-2) z.re]
  have hpI (i) : |(p i).re| < α+1 := (hstrip i).trans_lt (lt_add_one _)
  let φ (w : ℂ) := stripBlaschkeToDisk 2 k (A w)
  have hmap (w : ℂ) (hw : |w.re| < α+1) : φ w ∈ ball 0 1 :=
    stripBlaschkeToDisk_mem hk (by simpa using hwide w hw)
  have hφ (w : ℂ) (hw : |w.re| < α+1) : AnalyticAt ℂ φ w :=
    (stripBlaschkeToDisk_analytic (w₀ := 2) (w := A w) hk (by simpa using hwide w hw)).comp
      (analyticAt_const.add analyticAt_id)
  have hi : Injective (A ∘ p) := fun x y h ↦ hp (add_left_cancel h)
  obtain ⟨_, hne, hlt, hsum⟩ := continuedCompletedHeckeL_blaschke_family χ hk
    (A ∘ p) hi (fun i ↦ hwide _ (hpI i)) hz m hm
  obtain ⟨D, hD, hbound, hlim, hord⟩ := Blaschke.exists_holomorphic_disk_tails (φ ∘ p) m hne hlt hsum
  refine ⟨fun S ↦ D S ∘ φ, fun S w hw ↦ (hD S _ (hmap w hw)).comp (hφ w hw),
    fun S w hw ↦ hbound S _ (mem_ball_zero_iff.mp (hmap w hw)),
    fun w hw ↦ hlim _ (mem_ball_zero_iff.mp (hmap w hw)), ?_⟩
  intro S i hi
  have hd := hD S _ (hmap (p i) (hpI i))
  apply natCast_le_analyticOrderAt_comp hd (hφ _ (hpI i))
  obtain ⟨v, hv, he⟩ := hord S i hi
  apply (natCast_le_analyticOrderAt hd).mpr
  exact ⟨v, hv, he⟩

/-- For each compact character there is a sequence of bounded analytic cutoffs
on the widened strip. Apart from a finite set of actual strip-jet indices, each
cutoff kills the indicated order and every lower derivative on this component. -/
private theorem exists_spectralStripJet_tail_multipliers
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽) (ξ : PontryaginDual (ideleClassNorm F).ker)
    (a α s : ℝ) (hα : 0 ≤ α) :
    ∃ B : ℕ → ℂ → ℂ,
      (∀ n, DifferentiableOn ℂ (B n) {w | |w.re| < α+1}) ∧
      (∀ n w, |w.re| < α+1 → ‖B n w‖ ≤ 1) ∧
      (∀ w, |w.re| < α+1 → Tendsto (fun n ↦ B n w) atTop (𝓝 1)) ∧
      ∀ n, ∃ S : Finset (SpectralStripJetIndex χ a α s), ∀ j ∉ S, j.val.1 = ξ →
        ((j.val.2.2.2 + 1 : ℕ) : ℕ∞) ≤
          analyticOrderAt (B n) ((j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I) := by
  classical
  let J := SpectralStripJetIndex χ a α s
  let p (j : J) := (j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I
  let D := {j : J // j.val.1 = ξ}
  let Z := range (fun j : D ↦ p j.val)
  let order (w : ℂ) := (meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) ((a : ℂ) + w)).untop₀.toNat
  have hpa (j : J) : (a : ℂ) + p j = ((a+j.val.2.1 : ℝ) : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I := by
    simp [p, add_assoc]
  have hpre (j : J) : (p j).re = j.val.2.1 := by simp [p]
  have hpim (j : J) : (p j).im = j.val.2.2.1 := by simp [p]
  have hinside (w : Z) : |w.val.re| ≤ α := by
    obtain ⟨z, hz⟩ := w.property
    rw [← hz, hpre]
    exact abs_le.mpr (SpectralStripJetIndex.mem_strip_order_pos hα z.val).1
  have hpositive (w : Z) : 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) ((a : ℂ) + w.val) := by
    obtain ⟨z, hz⟩ := w.property
    rw [← hz, hpa]
    simpa only [show χ z.val.val.1 = χ ξ from congrArg χ z.property] using
      (SpectralStripJetIndex.mem_strip_order_pos hα z.val).2
  have hdeg (j : J) (hj : j.val.1 = ξ) : j.val.2.2.2 < order (p j) := by
    have h := j.property
    change j.val.2.2.2 < spectralStripMultiplicity α s j.val.2.1 _ at h
    rw [spectralStripMultiplicity] at h
    dsimp only [order]
    rw [hpa, ← hj]
    split_ifs at h with h₁ h₂
    · exact h
    · exact ((lt_spectralBoundaryMultiplicity _ _ _).mp h).1
    · omega
  have hfiber (w : Z) : {j : J | j.val.1 = ξ ∧ p j = w.val}.Finite := by
    let tuples := (Finset.range (order w.val)).image (fun k ↦ (ξ, w.val.re, w.val.im, k))
    apply (tuples.finite_toSet.preimage (f := fun j : J ↦ j.val) Subtype.val_injective.injOn).subset
    rintro j ⟨hj, h⟩
    refine Finset.mem_image.mpr ⟨j.val.2.2.2, Finset.mem_range.mpr (h ▸ hdeg j hj), ?_⟩
    exact Prod.ext hj.symm (Prod.ext ((congrArg Complex.re h).symm.trans (hpre j))
      (Prod.ext ((congrArg Complex.im h).symm.trans (hpim j)) rfl))
  let : Countable J := spectralStripJet_countable χ a α s
  let : Countable Z := Set.countable_range _
  obtain ⟨B, hB, hb, hl, ho⟩ := exists_hecke_strip_tail_multipliers (χ ξ) a α hα (fun w : Z ↦ w.val)
    Subtype.val_injective hinside hpositive (fun w ↦ order w.val) (fun _ ↦ le_rfl)
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset Z))
  refine ⟨fun n ↦ B (u n), fun n ↦ (hB _).differentiableOn, fun n ↦ hb (u n),
    fun w hw ↦ (hl w hw).comp hu, ?_⟩
  intro n
  let E : Set J := ⋃ w ∈ u n, {j | j.val.1 = ξ ∧ p j = w.val}
  have hE : E.Finite := (u n).finite_toSet.biUnion (fun w _ ↦ hfiber w)
  refine ⟨hE.toFinset, ?_⟩
  intro j hj hξ
  let w : Z := ⟨p j, ⟨⟨j,hξ⟩,rfl⟩⟩
  have ho' : w ∉ u n := by
    intro h
    apply hj
    exact hE.mem_toFinset.mpr <| mem_iUnion₂.mpr ⟨w,h,hξ,rfl⟩
  exact (ENat.natCast_le_natCast.mpr (hdeg j hξ)).trans (ho (u n) w ho')

end StripBlaschkeMultipliers

/-- The whole radial Hilbert range in an arbitrary prescribed character is in the
closure of ambient vectors with finite jet support. -/
private theorem stripTail_radial_mem_closure
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) (hsub : Icc (-α) α ⊆ I)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1))
    (hcut : ∀ n, ∃ S : Finset (Jχ(χ, a, α, s)), ∀ j ∉ S, j.val.1 = ω →
      ((dj(j) + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (b n) Zj(j))
    (L : Ws(α, s) →L[ℂ] W(-α, α, s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x)) :
    ∀ f, L f ∈ closure finiteJetMoments(χ, a, hα, hs) := by
  obtain ⟨P, -, hP, hrep⟩ := scalarIntervalSobolev_dense (-α) α s (stripI(hα)) hs I hI hInt hsub
  have h0 := hsub (show (0 : ℝ) ∈ Icc (-α) α from ⟨neg_nonpos.mpr hα, hα⟩)
  intro f
  refine hP.induction_on f ?_ (fun p ↦ ?_)
  · exact isClosed_closure.preimage L.continuous
  obtain ⟨q, hq, he⟩ := StripMultiplier.scalar_approximation hI hInt ⟨0, h0⟩ b hb hc hl p
  have ht : Tendsto (fun n ↦ L (P (q n))) l (𝓝 (L (P p))) :=
    ((L.continuous.tendsto _).comp (P.continuous.tendsto _)).comp hq
  apply mem_closure_of_tendsto ht
  refine .of_forall fun n ↦ ?_
  obtain ⟨S, hS⟩ := hcut n
  apply S.finite_toSet.subset
  intro j hj
  by_contra hjs
  apply hj
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hn := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp (hrep (q n))
  have hrep' : (L (P (q n)) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * (q n).val (logNorm x) := by
    refine (hL _).trans ?_
    apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
    filter_upwards [hn] with x hx using congrArg ((χ ω x : ℂ)⁻¹ * ·) hx
  change spectralSobolevPairing (L (P (q n))) ((stripU(χ, hα, hs)) j) = 0
  rw [stripTail_profile_pairing χ hχ ω hα hs hI hsub ν (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽) _ _ hrep' j]
  split_ifs with hω
  · have hz : Zj(j).re ∈ I := by simpa using hsub (j.mem_strip_order_pos hα).1
    rw [StripMultiplier.lower_jet_zero hI p (q n) (b n) (hb n) (he n) hInt Zj(j) hz
      (hS j hjs hω) (Nat.lt_succ_self _), mul_zero]
  · rfl

/-- The radial phase from the chosen base character lies in the same weighted L² space. -/
private theorem stripTail_twisted_radial (ξ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    {α s : ℝ} (f : Ws(α, s)) :
    ∃ g : Ws(α, s), (g : ℝ → ℂ) =ᵐ[volume] fun r ↦ (ξ (τ (sobolevLogEquiv r)) : ℂ) * f r := by
  let η := volume.withDensity fun r ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s r)
  have hac : volume ≪ η := withDensity_absolutelyContinuous'
    (continuous_intervalSobolevDensity' (-α) α s).measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun r ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos _ _ _ r)).ne')
  let w (r : ℝ) := (ξ (τ (sobolevLogEquiv r)) : ℂ)
  have hw : Continuous w := continuous_subtype_val.comp
    (ξ.continuous.comp (τ.continuous.comp sobolevLogEquiv.continuous))
  have hunit (r : ℝ) : ‖w r‖ = 1 := Circle.norm_coe (ξ (τ (sobolevLogEquiv r)))
  obtain ⟨M, hM⟩ := sobolev_unitary_mul η w hw.measurable hunit
  exact ⟨M f, hac.ae_eq (hM f)⟩

/-- On a split group, each physical compact-character tensor is one of the given
base-character lifts after a unitary radial phase correction. -/
private theorem stripTail_pure_realization
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ m𝔽)
    (κ : Measure C₁) [SFinite κ]
    (he : QuasiMeasurePreserving (fun p : C₁ × ℝ≥0ˣ ↦ (p.1 : C𝔽) * τ p.2) (κ.prod positiveRealHaar) μ𝔽)
    (f : Ws(α, s)) (ψ : PontryaginDual C₁) (v : Lp ℂ 2 κ) (hv : (v : C₁ → ℂ) =ᵐ[κ] fun k ↦ (ψ k : ℂ)) :
    ∃ (g : Ws(α, s)) (y : W(-α, α, s)),
      ((y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ψ⁻¹ x : ℂ)⁻¹ * g (logNorm x)) ∧
      (fun p : C₁ × ℝ≥0ˣ ↦ y ((p.1 : C𝔽) * τ p.2)) =ᵐ[κ.prod positiveRealHaar]
        fun p ↦ f (Real.log (p.2.val : ℝ)) * v p.1 := by
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let ω := ψ⁻¹
  let ξ := χ ω
  obtain ⟨g, hg⟩ := stripTail_twisted_radial ξ τ (α := α) (s := s) f
  obtain ⟨L, hL⟩ := stripTail_radial_lift ξ hα hs
  let y := L g
  refine ⟨g, y, hL g, ?_⟩
  have hsplit := he.ae_eq_comp (hL g)
  have hr := sobolevLog_ae hg
  have hrad := (Measure.quasiMeasurePreserving_snd (μ := κ) (ν := positiveRealHaar)).ae hr
  have hchar := (Measure.quasiMeasurePreserving_fst (μ := κ) (ν := positiveRealHaar)).ae hv
  let e (p : C₁ × ℝ≥0ˣ) := (p.1 : C𝔽) * τ p.2
  have hlog (p : C₁ × ℝ≥0ˣ) : logNorm (e p) = Real.log (p.2.val : ℝ) := by
    change Real.log ((m𝔽 ((p.1 : C𝔽) * τ p.2)).val : ℝ) = _
    rw [map_mul, show m𝔽 (p.1 : C𝔽) = 1 from p.1.property, one_mul, hτ]
  have hrt (t : ℝ≥0ˣ) : sobolevLogEquiv (Real.log (t.val : ℝ)) = t := by
    obtain ⟨u, rfl⟩ := sobolevLogEquiv.surjective t
    rw [sobolevLogEquiv_log]
  have hξ (k : C₁) : ξ (k : C𝔽) = (ψ k)⁻¹ := DFunLike.congr_fun (hχ ω) k
  filter_upwards [hsplit, hrad, hchar] with p hp hpr hpk
  change y (e p) = (ξ (e p) : ℂ)⁻¹ * g (logNorm (e p)) at hp
  change y (e p) = f (Real.log (p.2.val : ℝ)) * v p.1
  change g (Real.log (p.2.val : ℝ)) = (ξ (τ (sobolevLogEquiv _)) : ℂ) * f _ at hpr
  change v p.1 = (ψ p.1 : ℂ) at hpk
  rw [hp, hlog, hpr, hpk]
  change ((ξ ((p.1 : C𝔽) * τ p.2) : ℂ)⁻¹ * ((ξ (τ _) : ℂ) * f _)) = _
  rw [hrt, map_mul, Circle.coe_mul, hξ, Circle.coe_inv, mul_inv_rev, inv_inv]
  field_simp

open scoped TensorProduct InnerProductSpace in
/-- The canonical weighted Hilbert tensor map reads elementary product representatives
with respect to Tamagawa measure. -/
private theorem stripTail_weighted_tensor (α s : ℝ) (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ m𝔽)
    (κ : Measure C₁) [κ.IsHaarMeasure] (hκ : κ univ = 1) :
    let e (p : C₁ × ℝ≥0ˣ) := (p.1 : C𝔽) * τ p.2
    let m := κ.prod positiveRealHaar
    ∃ U : W(-α, α, s) ≃L[ℂ] UniformSpace.Completion (Ws(α, s) ⊗[ℂ] Lp ℂ 2 κ),
      QuasiMeasurePreserving e m μ𝔽 ∧ ∀ (f : Ws(α, s)) (v : Lp ℂ 2 κ) (y : W(-α, α, s)),
        ((y : C𝔽 → ℂ) ∘ e =ᵐ[m] fun p ↦ f (Real.log (p.2.val : ℝ)) * v p.1) →
        U y = ↑(f ⊗ₜ[ℂ] v) := by
  intro e m
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hemeas : Measurable e :=
    (measurable_subtype_coe.comp measurable_fst).mul (τ.continuous.measurable.comp measurable_snd)
  have he : MeasurePreserving e m ν :=
    ⟨hemeas, (canonicalModulatedHaar_eq_map_prod m𝔽 hm𝔽 τ hτ κ hκ).symm⟩
  have hqp : QuasiMeasurePreserving e m μ𝔽 :=
    ⟨hemeas.aemeasurable, by rw [he.map_eq]; exact Measure.absolutelyContinuous_isHaarMeasure ν μ𝔽⟩
  let ρ := intervalSobolevDensity (-α) α s
  let P := sobolevSplit_tensor m𝔽 hm𝔽 τ hτ κ hκ ρ (continuous_intervalSobolevDensity' _ _ _)
  let Tc := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 (-α) α s
  refine ⟨Tc.choose.trans P.choose.toContinuousLinearEquiv, hqp, fun f v y hy ↦ ?_⟩
  exact P.choose_spec f v (Tc.choose y) ((hqp.ae_eq_comp (Tc.choose_spec y).1).trans hy)

open scoped TensorProduct InnerProductSpace in
/-- The inverse-base-character lifts of the full radial weighted Hilbert spaces are total
in the arithmetic weighted Sobolev space, for every Sobolev exponent. -/
private theorem stripTail_angular_total
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (V : Submodule ℂ W(-α, α, s)) (hV : IsClosed (V : Set W(-α, α, s)))
    (hforms : ∀ (ω : PontryaginDual C₁) (f : Ws(α, s)) (y : W(-α, α, s)),
      ((y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x)) → y ∈ V) :
    ∀ y, y ∈ V := by
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker (m := m𝔽) hm𝔽)
  let κ : Measure C₁ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts C₁)
  let : IsProbabilityMeasure κ := ⟨Measure.haarMeasure_self⟩
  obtain ⟨τ, hτ⟩ := exists_section_of_surjective hm𝔽.1 hms𝔽
  obtain ⟨U, he, hU⟩ := stripTail_weighted_tensor (F := F) α s τ hτ κ Measure.haarMeasure_self
  obtain ⟨v, hv, hvc⟩ := dense_span_pontryaginDual_toLp κ
  refine mem_of_mem_tmul_dense_family (A := Ws(α, s)) (B := Lp ℂ 2 κ) U V hV v hv ?_
  intro f ψ
  let R := stripTail_pure_realization (F := F) χ hχ hα hs τ hτ κ he f ψ (v ψ) (hvc ψ)
  let g := R.choose
  let y := R.choose_spec.choose
  have hy : y ∈ V := hforms ψ⁻¹ g y R.choose_spec.choose_spec.1
  have ht := hU f (v ψ) y R.choose_spec.choose_spec.2
  exact ((congrArg U.symm ht.symm).trans (U.symm_apply_apply y)).symm ▸ hy

/-- Paper: Theorem 10.2.2.1, p. 446. Vectors with only finitely many nonzero
admitted Hecke jet moments are dense in the full weighted strip Sobolev space.
Deviation: In place of the finite-band argument on pp. 443 and 446, use bounded
Blaschke products on a wider strip. At a boundary zero, the index includes
only derivative orders satisfying the strict cutoff `2k + 1 < s` (F152). -/
theorem spectralStripJet_dense_finite_moment_support
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Dense finiteJetMoments(χ, a, hα, hs) := by
  let I := {r : ℝ | |r| < α + 1}
  have hI : I = Ioo (-(α + 1)) (α + 1) := by
    ext x
    change |x| < α + 1 ↔ -(α + 1) < x ∧ x < α + 1
    exact abs_lt
  have hopen : IsOpen I := hI ▸ isOpen_Ioo
  have hint : OrdConnected I := hI ▸ ordConnected_Ioo
  have hsub : Icc (-α) α ⊆ I := fun _ hr ↦ (abs_le.mpr hr).trans_lt (by linarith)
  let J := Jχ(χ, a, α, s)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let u (j : J) := (stripU(χ, hα, hs)) j
  let Lb (j : J) := (T.symm (u j)).toLinearMap
  have hLb (j : J) (x : W(-α, α, s)) : Lb j x = spectralSobolevPairing x (u j) :=
    (spectralSobolevPairing_dual (stripI(hα)) hs (T.symm (u j)) x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply (u j)))
  obtain ⟨S, hS⟩ := exists_submodule_finite_moment_support Lb
  have hset : (S : Set W(-α, α, s)) = finiteJetMoments(χ, a, hα, hs) := by
    rw [hS]
    ext x
    change (support (fun j : J ↦ Lb j x)).Finite ↔
      (support (fun j : J ↦ spectralSobolevPairing x (u j))).Finite
    simp only [hLb]
  have hcl : (S.topologicalClosure : Set W(-α, α, s)) = closure finiteJetMoments(χ, a, hα, hs) := by
    rw [← hset]
    rfl
  intro f
  change f ∈ closure finiteJetMoments(χ, a, hα, hs)
  rw [← hcl]
  apply stripTail_angular_total χ hχ hα hs S.topologicalClosure S.isClosed_topologicalClosure _ f
  intro ω g y hrep
  obtain ⟨L, hL⟩ := stripTail_radial_lift (χ ω) hα hs
  have hy : y = L g := by
    apply Lp.ext
    exact (withDensity_absolutelyContinuous _ _).ae_le (hrep.trans (hL g).symm)
  rw [hy, show L g ∈ S.topologicalClosure ↔ L g ∈ closure finiteJetMoments(χ, a, hα, hs) from
    Set.ext_iff.mp hcl _]
  obtain ⟨B, hb, hc, hl, hcut⟩ := exists_spectralStripJet_tail_multipliers χ ω a α s hα
  exact stripTail_radial_mem_closure χ hχ ω hα hs hopen hint hsub B hb hc hl hcut L hL g

/-- Paper: Theorem 10.2.2.1, p. 446. The constructed single-jet interpolants
span the geometric quotient densely under the reverse common-kernel inclusion.
Deviation: The ambient approximation uses strip Blaschke products in place of
the finite-band argument on p. 443. The reverse inclusion is the remaining
geometric approximation in the strip norm. -/
theorem spectralStripJet_dense_quotient_of_reverse (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hker : ∀ x : W(-α, α, s), (∀ j : Jχ(χ, a, α, s), spectralSobolevPairing x ((stripU(χ, hα, hs)) j) = 0) →
      x ∈ Θ(a, stripI(hα), hs)) :
    let v (i : Jχ(χ, a, α, s)) := (spectralStripJet_singleInterpolant χ hχ hα hs i).choose
    Dense (Submodule.span ℂ (range fun i ↦ (Θ(a, stripI(hα), hs)).mkQ (v i)) :
      Set (spectralSobolevQuotient F a (stripI(hα)) hs)) := by
  intro v
  let J := Jχ(χ, a, α, s)
  let N := Θ(a, stripI(hα), hs)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let u (j : J) := (stripU(χ, hα, hs)) j
  let L (j : J) := (T.symm (u j)).toLinearMap
  have hL (j : J) (x : W(-α, α, s)) : L j x = spectralSobolevPairing x (u j) :=
    (spectralSobolevPairing_dual (stripI(hα)) hs (T.symm (u j)) x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply (u j)))
  apply dense_span_quotient_biorthogonal_of_finite_support N.mkQL N.mkQ_surjective v L
  · intro i j
    rw [hL]
    by_cases he : i = j
    · subst j
      simpa only [ite_true] using (spectralStripJet_singleInterpolant χ hχ hα hs i).choose_spec i
    · simpa only [ite_eq_right he, ite_eq_right (Ne.symm he)] using
        (spectralStripJet_singleInterpolant χ hχ hα hs i).choose_spec j
  · intro x hx
    exact (spectralSobolevQuotient_eq_zero a (stripI(hα)) hs x).mpr
      (hker x (fun j ↦ (hL j _).symm.trans (hx j)))
  · apply (spectralStripJet_dense_finite_moment_support χ hχ a α s hα hs).mono
    intro x hx
    change (support (fun j : J ↦ L j x)).Finite
    change (support (fun j : J ↦ spectralSobolevPairing x (u j))).Finite at hx
    simpa only [hL] using hx


/-- Paper: Theorem 10.2.2.1, p. 446. Common-kernel perturbations of the constructed
interpolants can be chosen so that their classes span densely in the geometric quotient.
Deviation: Finite moment support is dense by the preceding cutoff argument. The reverse
common-kernel inclusion then gives density of the single interpolants themselves. -/
private theorem spectralStripJet_interpolantDensity (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := Jχ(χ, a, α, s)
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    let v (i : J) := (spectralStripJet_singleInterpolant χ hχ hα hs i).choose
    ∃ r : J → W(-α, α, s), (∀ i j, spectralSobolevPairing (r i) (u j) = 0) ∧
      Dense (Submodule.span ℂ (range fun i ↦ (Θ(a, stripI(hα), hs)).mkQ (v i + r i)) :
        Set (spectralSobolevQuotient F a (stripI(hα)) hs)) := by
  intro J u v
  have hd := spectralStripJet_dense_quotient_of_reverse χ hχ hα hs (a := a)
    (fun x hx ↦ (spectralStripJet_commonKernel χ hχ hα hs x).mpr hx)
  refine ⟨fun _ ↦ 0, fun _ j ↦ ?_, ?_⟩
  · let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
    let L := T.symm (u j)
    exact ((spectralSobolevPairing_dual (stripI(hα)) hs L 0).2.trans
      (congrArg (spectralSobolevPairing (0 : W(-α, α, s))) (T.apply_symm_apply (u j)))).symm.trans L.map_zero
  · simpa only [add_zero] using hd

end StripSingleJets

/-- Paper: Theorem 10.2.2.1, p. 446. The individual strip jets admit
interpolants whose classes span densely in the geometric quotient.
Deviation: Density follows from wider-strip Blaschke products and the reverse
inclusion of the common kernel in the geometric theta closure (Theorem 10.2.2.1). -/
theorem spectralStripJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    JetInterpolation(J, a, stripI(hα), hs, u) := by
  intro J u
  let v (i : J) := (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let L (j : J) := T.symm (u j)
  have hL (j : J) (x : W(-α, α, s)) : L j x = spectralSobolevPairing x (u j) :=
    (spectralSobolevPairing_dual (stripI(hα)) hs (L j) x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply (u j)))
  let D (y : J → W(-α, α, s)) : Prop :=
    Dense (Submodule.span ℂ (range fun i ↦ (Θ(a, stripI(hα), hs)).mkQ (y i)) :
      Set (spectralSobolevQuotient F a (stripI(hα)) hs))
  have hv (i : J) : L i (v i) = 1 := (hL i _).trans (by
    simpa only [ite_true] using (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose_spec i)
  have hz (i j : J) (hij : i ≠ j) : L j (v i) = 0 := (hL j _).trans (by
    simpa only [ite_eq_right (Ne.symm hij)] using
      (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose_spec j)
  obtain ⟨r, hr, hd⟩ := spectralStripJet_interpolantDensity χ _hχ hα hs (a := a)
  obtain ⟨y, hy, hy', hd'⟩ := (StripInterpolation.density_iff
    (fun j ↦ (L j).toLinearMap) D v hv hz).mpr ⟨r, fun i j ↦ (hL j _).trans (hr i j), hd⟩
  exact ⟨y, fun i ↦ (hL i _).symm.trans (hy i),
    fun i j hij ↦ (hL j _).symm.trans (hy' i j hij), hd'⟩

/-- At width zero the real offset of each strip jet is zero, and its remaining
indices give exactly one line jet with the same function representative. -/
private theorem spectralLineJet_zeroWidth_indices (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a s : ℝ) :
    ∃ e : SpectralLineJetIndex χ a s ≃ SpectralStripJetIndex χ a 0 s,
      ∀ i, stripJet(χ, e i) = lineJet(χ, i) := by
  let L := SpectralLineJetIndex χ a s
  let Z := SpectralStripJetIndex χ a 0 s
  have hoff (j : Z) : j.val.2.1 = 0 := by
    simpa using (SpectralStripJetIndex.mem_strip_order_pos (le_refl (0 : ℝ)) j).1
  have hmult (n : ℕ) : spectralStripMultiplicity 0 s 0 n = spectralBoundaryMultiplicity s n :=
    spectralStripMultiplicity_boundary le_rfl (Or.inr rfl) s n
  let e : L ≃ Z :=
    { toFun := fun i ↦ ⟨(i.val.1, 0, i.val.2.1, i.val.2.2), by
        simpa only [add_zero, hmult] using i.property⟩
      invFun := fun j ↦ ⟨(j.val.1, j.val.2.2.1, j.val.2.2.2), by
        simpa only [hoff j, add_zero, hmult] using j.property⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun j ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hoff j).symm rfl)) }
  exact ⟨e, fun _ ↦ rfl⟩

/-- Transport a statement about the reindexed reciprocal-weight vectors from
the interval [−0, 0] to the identical line Sobolev space. -/
private theorem spectralLineJet_zeroWidth_transport (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a : ℝ) {s : ℝ} (hs : 1 < s)
    (P : ∀ {l : ℝ}, l ≤ 0 → (SpectralLineJetIndex χ a s → W'(l, 0, s)) → Prop)
    (h : ∀ (e : SpectralLineJetIndex χ a s ≃ SpectralStripJetIndex χ a 0 s),
      P (stripI(le_refl (0 : ℝ))) (fun i ↦ stripU(χ, le_refl (0 : ℝ), lineHs(hs)) (e i))) :
    P (le_refl (0 : ℝ)) (lineU(χ, hs)) := by
  obtain ⟨e, he⟩ := spectralLineJet_zeroWidth_indices χ a s
  let claim (l : ℝ) (hl : l ≤ 0) := ∀ hm : ∀ i : SpectralLineJetIndex χ a s,
    MemLp (lineJet(χ, i)) 2 L2μ'(l, 0, s), P hl (fun i ↦ (hm i).toLp (lineJet(χ, i)))
  have hstrip : claim (-0) (stripI(le_refl (0 : ℝ))) := by
    intro hm
    have eqv : (fun i ↦ stripU(χ, le_refl (0 : ℝ), lineHs(hs)) (e i)) =
        fun i ↦ (hm i).toLp (lineJet(χ, i)) := by
      funext i
      exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (he i)))
    exact eqv ▸ h e
  have transport (l : ℝ) (hl : l ≤ 0) (hl0 : l = 0) : claim l hl → claim 0 le_rfl := by
    subst l
    exact id
  exact transport (-0) _ neg_zero hstrip (spectralLineJet_memLp χ hs)

/-- Paper: Theorem 10.2.1.1, pp. 440–443. The weighted theta closure is
the common kernel of the admitted line jets.
Gap: The line approximation required on p. 443 is the width-zero case of the strip common-kernel assertion. -/
theorem spectralLineJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let u : SpectralLineJetIndex χ a s → W'(0, 0, s) := lineU(χ, hs)
    JetKernel(a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  apply spectralLineJet_zeroWidth_transport χ a hs
    (fun hl u ↦ JetKernel(a, hl, lineHs(hs), u))
  intro e y
  refine (spectralStripJet_commonKernel (a := a) χ _hχ (le_refl (0 : ℝ)) (lineHs(hs)) y).trans ?_
  exact e.surjective.forall

/-- Paper: Theorem 10.2.1.1, pp. 440–443. Single-jet interpolants have
representatives whose images span a dense subspace of the line quotient.
Gap: The interpolation and density asserted on p. 443 follow from the corresponding
strip assertion at width zero. -/
theorem spectralLineJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let u : J → W'(0, 0, s) := lineU(χ, hs)
    JetInterpolation(J, a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  apply spectralLineJet_zeroWidth_transport χ a hs
    (fun hl u ↦ JetInterpolation(SpectralLineJetIndex χ a s, a, hl, lineHs(hs), u))
  intro e
  obtain ⟨v, hv, hc, hd⟩ :=
    spectralStripJet_denseInterpolants (a := a) χ _hχ (le_refl (0 : ℝ)) (lineHs(hs))
  refine ⟨v ∘ e, fun i ↦ hv (e i), fun i j hij ↦ hc (e i) (e j) (e.injective.ne hij), ?_⟩
  let q := (Θ(a, stripI(le_refl (0 : ℝ)), lineHs(hs))).mkQ
  change Dense (Submodule.span ℂ (range ((fun j ↦ q (v j)) ∘ e)) :
    Set (spectralSobolevQuotient F a (stripI(le_refl (0 : ℝ))) (lineHs(hs))))
  rwa [e.surjective.range_comp]

/-- Paper: Theorem 10.2.1.1 and Terminology 10.2.1.1, p. 440. The a-line
jets represent quotient functionals and admit a Markushevich biorthogonal family.
Deviation: Index directly by the admitted jets, so reindexing permits any
enumeration, including finite and empty families. Apply the strict cutoff. -/
theorem spectralLineMarkushevichBasis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let Q := spectralSobolevQuotient F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    let D := spectralSobolevDualEmbedding F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    Countable J ∧ ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j)) := by
  exact ⟨spectralLineJet_countable χ a s, spectralSobolevQuotient_basis_of_interpolation a
    (le_rfl (a := (0 : ℝ))) (lineHs(hs)) (lineU(χ, hs))
    (spectralLineJet_commonKernel χ hχ hs) (spectralLineJet_denseInterpolants χ hχ hs)⟩

/-- Paper: Corollary 10.2.1.4, p. 444. The a-line basis in the quotient dual
is normalized in the norm of its realization in the negative space.
Deviation: Apply the strict cutoff and allow finite or empty index types. -/
theorem spectralLineMarkushevichBasis_normalized
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let Q := spectralSobolevQuotient F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    let D := spectralSobolevDualEmbedding F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D (Λ j) = (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))) ∧
      IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) := by
  obtain ⟨x, Λ, hB, hD⟩ := (spectralLineMarkushevichBasis (a := a) χ _hχ hs).2
  obtain ⟨C, hC, hbound⟩ := spectralLineJet_annulus (a := a) χ _hχ hs
  refine ⟨x, Λ, hB, hD, ⟨C, ?_⟩, ⟨C⁻¹, inv_pos.mpr hC, ?_⟩⟩
  · intro j
    simpa only [hD j] using (hbound j).2
  · intro j
    simpa only [hD j] using (hbound j).1

/-- Paper: Theorem 10.2.2.1 and Terminology 10.2.2.1, p. 446. The strip
jets represent quotient functionals and admit a Markushevich biorthogonal family.
Deviation: Exclude the divergent endpoint and allow finite or empty enumerations. -/
theorem spectralStripMarkushevichBasis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let Q := spectralSobolevQuotient F a (neg_nonpos.mpr hα |>.trans hα) hs
    let D := spectralSobolevDualEmbedding F a (neg_nonpos.mpr hα |>.trans hα) hs
    Countable J ∧ ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)) := by
  exact ⟨spectralStripJet_countable χ a α s, spectralSobolevQuotient_basis_of_interpolation a
    (stripI(hα)) hs (stripU(χ, hα, hs))
    (spectralStripJet_commonKernel χ hχ hα hs) (spectralStripJet_denseInterpolants χ hχ hα hs)⟩

private theorem spectralStripJet_norm_sq (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    ‖(spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))‖ ^ 2 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
  let u := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let f : ℝ → ℝ := fun x ↦
    Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) := spectralJet_lp_norm_sq u
  have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) =
      ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
        ∂(L2μ'(-α, α, s)) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (spectralStripJet_memLp χ hα hs j)] with g hg
    rw [hg, spectralZeroJet_norm_sq]
  have h3 : ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
      ∂(L2μ'(-α, α, s)) = ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 := by
    rw [integral_withDensity_eq_integral_toReal_smul
      ((symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal)
      (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
    dsimp only [f]
    rw [smul_eq_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g)).le),
      mul_comm, stripJet_integrand_eq hα]
  have hmp : MeasurePreserving (fun g : C𝔽 ↦ logNorm g) ν volume := by
    rw [hν]
    exact sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hlogm : AEMeasurable (fun g : C𝔽 ↦ logNorm g) ν :=
    (continuous_logModule' m𝔽).measurable.aemeasurable
  have hν_eq : ∫ g : C𝔽, f (logNorm g) ∂ν = ∫ x : ℝ, f x ∂volume := by
    rw [← hmp.map_eq,
      integral_map hlogm
        (stripJet_integrand_continuous α s j.val.2.1 j.val.2.2.2).aestronglyMeasurable]
  have h4 : ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 = (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, f x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  exact h1.trans (h2.trans (h3.trans h4))

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A single
positive lower bound applies to the norms of all the strip jet classes.
Deviation: Use the strip zeros and reciprocal strip norm of Theorem 10.2.2.1.
Disjointness from the open ball also applies to the empty family. -/
theorem spectralStripJet_lowerBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : SpectralStripJetIndex χ a α s,
      let u := (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) j).toLp (stripJet(χ, j))
      c ≤ ‖u‖ := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := le_of_lt (zero_lt_one.trans hs)
  let c₀ : ℝ := Real.exp (-8 * α) * ((5 : ℝ) ^ (s / 2))⁻¹
  have hc₀ : 0 < c₀ := mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  let c : ℝ := Real.sqrt ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀)
  refine ⟨c, Real.sqrt_pos.mpr (mul_pos hfac_pos hc₀), fun j ↦ ?_⟩
  dsimp only
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  have hf_int : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
    spectralStripJet_integrable hα hs₀ hcond
  have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c₀) volume :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hb : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
  have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c₀) x ≤
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    intro x
    by_cases hx : x ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem hx]
      have hxpos : 0 ≤ x := by linarith [hx.1]
      have hexp : Real.exp (-8 * α) ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) := by
        rw [abs_of_nonneg hxpos]
        exact Real.exp_le_exp.mpr (by nlinarith [hb.1, hx.1, hx.2])
      have hpow : (1 : ℝ) ≤ x ^ (2 * j.val.2.2.2) := one_le_pow₀ hx.1
      have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith [hx.1, hx.2]
      have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith)
      have hinv : ((5 : ℝ) ^ (s / 2))⁻¹ ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
      have hprod : Real.exp (-8 * α) ≤
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := by
        calc
          Real.exp (-8 * α) = Real.exp (-8 * α) * 1 := (mul_one _).symm
          _ ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) :=
            mul_le_mul hexp hpow zero_le_one (Real.exp_pos _).le
      exact mul_le_mul hprod hinv
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by norm_num) _).le)
        (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hint_le : c₀ ≤ ∫ x : ℝ,
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
    have h1 := integral_mono hind_int hf_int hle
    have h2 : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c₀) x ∂volume = c₀ := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      norm_num
    linarith
  have hsq : (Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀ ≤
      ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by
    rw [spectralStripJet_norm_sq χ hα hs₀ j ν rfl]
    exact mul_le_mul_of_nonneg_left hint_le hfac_pos.le
  calc
    c = Real.sqrt ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀) := rfl
    _ ≤ Real.sqrt (‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ :=
      Real.sqrt_sq (norm_nonneg _)

/-- Paper: Proposition 10.2.2.2, pp. 446–447. A uniform strip estimate requires a
bound on admitted jet orders and a boundary margin for the nonintegrable powers.
Gap: The paper supplies neither estimate for the actual completed Hecke divisor. -/
theorem spectralStripJet_order_and_margin (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (_hα : 0 ≤ α) (_hs : 1 < s) :
    ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a α s,
      j.val.2.2.2 ≤ K ∧ ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) := by sorry

/-- Paper: Proposition 10.2.2.2, pp. 446–447. Finitely many integrable
boundary powers and a positive exponential margin on all other powers give
a uniform norm bound. -/
theorem spectralStripJet_upperBound_of_margin (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (K : ℕ) (δ : ℝ) (_hδ : 0 < δ)
    (_h : ∀ j : SpectralStripJetIndex χ a α s, j.val.2.2.2 ≤ K ∧
      ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralStripJetIndex χ a α s,
      ‖(spectralStripJet_memLp χ hα (lineHs(hs)) j).toLp (stripJet(χ, j))‖ ≤ C := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := lineHs(hs)
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let M_bdry : ℝ := ∑ m ∈ Finset.range N,
    ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume
  let M_int : ℝ :=
    ∫ x : ℝ, Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) ∂volume
  have hfac_nonneg : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) := NNReal.coe_nonneg _
  have hM_bdry_nonneg : 0 ≤ M_bdry :=
    Finset.sum_nonneg fun m _ ↦ integral_nonneg fun x ↦
      mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hM_int_nonneg : 0 ≤ M_int :=
    integral_nonneg fun x ↦
      mul_nonneg (Real.exp_pos _).le (add_nonneg zero_le_one (Even.pow_nonneg (even_two_mul K) x))
  have hM_int_integrable : Integrable (fun x : ℝ ↦ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)))
      volume := by
    have h0 := integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) 0
    have hK := integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) K
    refine (h0.add hK).congr (ae_of_all _ fun x ↦ ?_)
    change Real.exp (-(2 * δ) * |x|) * x ^ (2 * 0) +
        Real.exp (-(2 * δ) * |x|) * x ^ (2 * K) =
      Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K))
    simp only [mul_zero, pow_zero, mul_one]
    ring
  let B : ℝ := 1 + (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int)
  have hB_pos : 0 < B := by
    have : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_nonneg hfac_nonneg (add_nonneg hM_bdry_nonneg hM_int_nonneg)
    linarith
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB_pos, fun j ↦ ?_⟩
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  have hf_int : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
    spectralStripJet_integrable hα hs₀ hcond
  have hint_bound : ∫ x : ℝ,
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry + M_int := by
    by_cases hk : (j.val.2.2.2 : ℝ) < (s - 1) / 2
    · have hk' : 2 * (j.val.2.2.2 : ℝ) + 1 < s := by linarith
      have hb : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
      have hba : |j.val.2.1| ≤ α := abs_le.mpr hb
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
          ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
        refine integral_mono hf_int (integrable_pow_mul_rpow_inv hk') fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ α * |x| := by
          calc
            j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ α * |x| := mul_le_mul_of_nonneg_right hba (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        rw [mul_assoc]
        calc
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
              (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
            ≤ 1 * (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
              mul_le_mul_of_nonneg_right hexp
                (mul_nonneg (Even.pow_nonneg (even_two_mul _) x)
                  (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
          _ = x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _
      have hjN : j.val.2.2.2 ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_ceil.mpr hk)
      have h2 : ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry :=
        Finset.single_le_sum
          (f := fun m ↦ ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume)
          (fun m _ ↦ integral_nonneg fun x ↦
            mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
              (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))) hjN
      linarith
    · have hk_ge : (s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) := not_lt.mp hk
      have hmargin : |j.val.2.1| ≤ α - δ := (_h j).2 hk_ge
      have hkK : j.val.2.2.2 ≤ K := (_h j).1
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_int := by
        refine integral_mono hf_int hM_int_integrable fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ (α - δ) * |x| := by
          calc
            j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ (α - δ) * |x| := mul_le_mul_of_nonneg_right hmargin (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ Real.exp (-(2 * δ) * |x|) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hpow : x ^ (2 * j.val.2.2.2) ≤ 1 + x ^ (2 * K) := by
          have hxa : x ^ (2 * j.val.2.2.2) = |x| ^ (2 * j.val.2.2.2) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          have hxaK : x ^ (2 * K) = |x| ^ (2 * K) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          rw [hxa, hxaK]
          rcases le_total |x| 1 with hx1 | hx1
          · have : |x| ^ (2 * j.val.2.2.2) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
            linarith [pow_nonneg (abs_nonneg x) (2 * K)]
          · have : |x| ^ (2 * j.val.2.2.2) ≤ |x| ^ (2 * K) :=
              pow_le_pow_right₀ hx1 (Nat.mul_le_mul_left 2 hkK)
            linarith
        have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
        calc
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
              ((1 + x ^ 2) ^ (s / 2))⁻¹
            ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * 1 :=
              mul_le_mul_of_nonneg_left hinv_le
                (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
          _ = Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := mul_one _
          _ ≤ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) :=
              mul_le_mul hexp hpow (Even.pow_nonneg (even_two_mul _) x) (Real.exp_pos _).le
      linarith
  have hsq : ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 ≤ B := by
    rw [spectralStripJet_norm_sq χ hα hs₀ j ν rfl]
    have hmul : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
        (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_le_mul_of_nonneg_left hint_bound hfac_nonneg
    dsimp only [B]
    linarith
  calc
    ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖
      = Real.sqrt (‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsq

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A single upper
bound applies to the norms of all the strip jet classes.
Deviation: Use the strip zeros and both cutoff equations of Theorem 10.2.2.1,
with the reciprocal strip norm throughout. -/
theorem spectralStripJet_upperBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralStripJetIndex χ a α s,
      let u := (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) j).toLp (stripJet(χ, j))
      ‖u‖ ≤ C := by
  obtain ⟨K, δ, hδ, h⟩ := spectralStripJet_order_and_margin (a := a) χ _hχ hα hs
  exact spectralStripJet_upperBound_of_margin χ hα hs K δ hδ h

/-- Paper: Corollary 10.2.2.3, p. 447. The strip basis in the quotient dual
is normalized in the norm of its realization in the reciprocal strip space.
Deviation: Use the strip zeros and cutoff of Theorem 10.2.2.1. The ambient
negative space is the reciprocal strip space as specified by the pairing. -/
theorem spectralStripMarkushevichBasis_normalized
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let hs₀ := le_of_lt (zero_lt_one.trans hs)
    let J := SpectralStripJetIndex χ a α s
    let Q := spectralSobolevQuotient F a (neg_nonpos.mpr hα |>.trans hα) hs₀
    let D := spectralSobolevDualEmbedding F a (neg_nonpos.mpr hα |>.trans hα) hs₀
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))) ∧
      IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) := by
  obtain ⟨x, Λ, hB, hD⟩ := (spectralStripMarkushevichBasis (a := a) χ _hχ hα
    (lineHs(hs))).2
  obtain ⟨C, _, hupper⟩ := spectralStripJet_upperBound (a := a) χ _hχ hα hs
  obtain ⟨c, hc, hlower⟩ := spectralStripJet_lowerBound (a := a) χ _hχ hα hs
  refine ⟨x, Λ, hB, hD, ⟨C, ?_⟩, ⟨c, hc, ?_⟩⟩
  · intro j
    simpa only [hD j] using hupper j
  · intro j
    simpa only [hD j] using hlower j

end RiemannMasullo
