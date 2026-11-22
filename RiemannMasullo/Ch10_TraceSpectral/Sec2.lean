module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
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
Deviation: The line uses the compact interval with both endpoints zero, as in §9.2. -/
abbrev spectralSobolevQuotient (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :=
  W(l, r, s) ⧸ Θ(a, hI, hs)

/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. A Sobolev vector has
zero spectral class exactly when it is in the closed weighted theta subspace. -/
theorem spectralSobolevQuotient_eq_zero (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (f : W(l, r, s)) : Θ(a, hI, hs).mkQ f = 0 ↔ f ∈ Θ(a, hI, hs) :=
  Submodule.Quotient.mk_eq_zero _

variable (F) in
/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. Divide the ambient
norm-one isotype by its closed weighted theta subspace. -/
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
    Integrable (fun g ↦ f g * T Λ g) μ𝔽 ∧ Λ f = pair(f, T Λ) := by sorry

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
      ∃ f : Wω(hI, hs, ω), pair(f.val, u) ≠ 0 := by sorry

variable (F) in
/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pull a functional
back along the quotient map and realize it in the reciprocal-weight Sobolev space. -/
def spectralSobolevDualEmbedding (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    StrongDual ℂ (spectralSobolevQuotient F a hI hs) →ₗ[ℂ] W'(l, r, s) :=
  (T(l, r, s, hI, hs)).toLinearEquiv.toLinearMap.comp
    ((Θ(a, hI, hs)).mkQL.precomp ℂ).toLinearMap

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pullback along the
quotient identifies its strong dual isometrically with the theta annihilator. -/
theorem spectralSobolevDualEmbedding_isometry_range (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) :
    let D := spectralSobolevDualEmbedding F a hI hs
    Isometry D ∧ range D = {u | ∀ f ∈ Θ(a, hI, hs), pair(f, u) = 0} := by sorry

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

/-- Paper: Theorem 10.2.1.1, p. 440. The admitted a-line jets are elements of
the reciprocal-weight Hilbert space.
Deviation: Exclude the divergent endpoint of (10.2.1.6). -/
theorem spectralLineJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (_hs : 1 < s) (j : SpectralLineJetIndex χ a s) :
    MemLp (lineJet(χ, j)) 2 (L2μ'(0, 0, s)) := by sorry

-- For a family of admitted jets u, these are the two analytic inputs to
-- the Hilbert-space argument. Interpolants are lifted to the ambient space.
local notation "JetKernel(" a ", " hI ", " hs ", " u ")" =>
  (∀ f, f ∈ Θ(a, hI, hs) ↔ ∀ j, spectralSobolevPairing (F := F) f (u j) = 0)
local notation "JetInterpolation(" J ", " a ", " hI ", " hs ", " u ")" =>
  (∃ v : J → W(_, _, _), (∀ i, spectralSobolevPairing (F := F) (v i) (u i) = 1) ∧
    (∀ i j, i ≠ j → spectralSobolevPairing (F := F) (v i) (u j) = 0) ∧
    Dense (Submodule.span ℂ (range (fun i ↦ (Θ(a, hI, hs)).mkQ (v i))) :
      Set (spectralSobolevQuotient F a hI hs)))

/-- Paper: Theorems 10.2.1.1 and 10.2.2.1, pp. 440, 446. A common kernel
identifies the closed dual span in the Hilbert quotient. A dense family of
interpolants then supplies the other half of the Markushevich basis. -/
theorem spectralSobolevQuotient_basis_of_interpolation {J : Type*}
    (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) (u : J → W'(l, r, s))
    (_hK : JetKernel(a, hI, hs, u)) (_hV : JetInterpolation(J, a, hI, hs, u)) :
    let Q := spectralSobolevQuotient F a hI hs
    let D := spectralSobolevDualEmbedding F a hI hs
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = u j := by sorry

local notation "lineHs(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "lineU(" χ ", " hs ")" =>
  (fun j ↦ (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j)))

/-- Paper: Theorem 10.2.1.1, pp. 440–443. The weighted theta closure is
the common kernel of the admitted line jets.
Gap: The proof on p. 443 does not identify this closure in the line norm. -/
theorem spectralLineJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let u : SpectralLineJetIndex χ a s → W'(0, 0, s) := lineU(χ, hs)
    JetKernel(a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by sorry

/-- Paper: Theorem 10.2.1.1, pp. 440–443. Single-jet interpolants have
representatives whose images span a dense subspace of the line quotient.
Gap: The asserted finite-band adjoint range does not supply these interpolants
and their density. -/
theorem spectralLineJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let u : J → W'(0, 0, s) := lineU(χ, hs)
    JetInterpolation(J, a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by sorry

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

section TestDuality

local notation "E" => ModulatedExponentialDecay m𝔽 univ
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω
local notation "ℬ₀" => ↥(adelePolarSubspace F)

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
            fun g ↦ (ω⁻¹ k : ℂ) * u g) → T u = 0 → u = 0 := by sorry

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
    Injective D ∧ ∀ Λ (φ : Eω(ω)) (f : ℬ₀), φ.val.val = homogeneousAdelicTheta ω f.val → D Λ φ = 0 := by sorry

end TestDuality

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
          φ.val (ideleClassNormTwist (χ j.val.1) z)) (shift(a, j.val.2.1)) := by sorry

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
      ∀ f : E, Tendsto (fun n ↦ P n f) atTop (𝓝 f) := by sorry

/-- Paper: Proposition 10.2.1.3 and (10.2.1.12), p. 443. A single annulus
contains all the a-line jet classes.
Deviation: Use the truncated multiplicity intended by the reference to
(10.2.1.6). The lower bound asserts disjointness from the open ball, which
also makes sense for an empty zero set. -/
theorem spectralLineJet_annulus (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralLineJetIndex χ a s,
      let u := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
      C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C := by sorry

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

-- TODO(paper-gap): The general claim about the Schauder property on p. 444
-- lacks a proof. The primal normalization invoked again on p. 451 is false:
-- close simple critical-line zeta zeros give jets at distance tending to zero,
-- so the corresponding biorthogonal vector norms are unbounded (ERRATA R5).

section BandProjections

attribute [local instance] instDualMeasurableSpaceSec3

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
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by sorry

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

/-- Paper: Theorem 10.2.2.1, p. 446. The admitted strip jets are
square-integrable for the reciprocal strip weight.
Deviation: Exclude the divergent boundary endpoint of (10.2.2.5). -/
theorem spectralStripJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s) :
    MemLp (stripJet(χ, j)) 2 (L2μ'(-α, α, s)) := by sorry

local notation "stripI(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripU(" χ ", " hα ", " hs ")" =>
  (fun j ↦ (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)))

/-- Paper: Theorem 10.2.2.1, p. 446. The weighted theta closure is the common
kernel of all surviving strip evaluations.
Gap: The complementary projections of §9.3 exhaust the orthogonal of the
common kernel. Identifying this kernel with the geometric theta closure
requires a separate approximation in the strip norm. -/
theorem spectralStripJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    JetKernel(a, stripI(hα), hs, u) := by sorry

/-- Paper: Theorem 10.2.2.1, p. 446. The individual strip jets admit
interpolants whose classes span densely in the geometric quotient.
Gap: Orthogonal exhaustion by the evaluation representers does not establish
interpolation and density of the biorthogonal vectors. -/
theorem spectralStripJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    JetInterpolation(J, a, stripI(hα), hs, u) := by sorry

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

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A single
positive lower bound applies to the norms of all the strip jet classes.
Deviation: Use the strip zeros and reciprocal strip norm of Theorem 10.2.2.1.
Disjointness from the open ball also applies to the empty family. -/
theorem spectralStripJet_lowerBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : SpectralStripJetIndex χ a α s,
      let u := (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) j).toLp (stripJet(χ, j))
      c ≤ ‖u‖ := by sorry

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
      ‖(spectralStripJet_memLp χ hα (lineHs(hs)) j).toLp (stripJet(χ, j))‖ ≤ C := by sorry

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
