module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a

import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
import RiemannMasullo.ForMathlib.Analysis.Complex.SeparatedExponentialFactor
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.MellinInversion
import RiemannMasullo.ForMathlib.Analysis.MellinTransform
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Int

/-!
# Isolated statements for the separate place sums in §7.1.2

Statements and partial results for open problem #7279 (Theorem 7.1.2.3, pp. 317–323, ERRATA I210).
Nothing in the library imports this file (`AGENTS.md`, "False statements and gaps").

The printed expansion counts a pole shared by two places under each of them, which is refuted
(`Sec1a_Printed.lean`, F88). Counting each pole once requires an assignment of poles to
contributing places. We state the repaired separately summed expansion as a proposition
parameterized by that assignment (asserting nothing), prove that convergent assignments always
share the same total and agree with the contour shift, classify when convergence is independent
of the assignment (including unconditionally over `ℚ`), prove uniform convergence for every
assignment under a summable majorant, establish uniform pole discreteness over any single
rational prime, and prove the exact lattice arithmetic equivalence behind the Gaussian-field
obstruction in #7279. For a single residue characteristic the sections below split common
residue windows by finite interpolation and prove absolute convergence of the place sums.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped BigOperators NNReal Asymptotics

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "Tests" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "normₛ" => sIdeleQuotientNorm F S
local notation "chart(" χ ")" => quasiCharacterNormTwist (G := Jₛ) normₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
local notation "Places" => InfinitePlace F ⊕ S

local instance isolatedCh07Sec1aNormOneMeasurableSpace : MeasurableSpace (normₛ).ker := borel _
local instance isolatedCh07Sec1aNormOneHaar : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

/-! ## Contributing places and valid pole assignments -/

/-- Paper: Lemma 7.1.2.2, pp. 316–317. Explicit local-pole condition indicating that a place
in `InfinitePlace F ⊕ S` contributes the pole `a` of `sLocalRhoFactor (chart(χ) ·)`.
Deviation: Uses the repaired complex-place sign and shifted finite-place lattice of
`sLocalRhoFactor_poles_iff`. -/
def sLocalPoleContributes (χ : PontryaginDual Jₛ) : Places → ℂ → Prop :=
  Sum.elim
    (fun w a ↦
      (∃ (hw : w.IsReal) (n : ℕ),
        let p := (realLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        a = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)) ∨
      (∃ (hw : w.IsComplex) (n : ℕ),
        let p := (complexLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        a = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)))
    (fun v a ↦
      ∃ (m : ℤ) (t : ℝ),
        let period := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
        t ∈ Ico 0 period ∧
          (∀ x : (v.val.adicCompletion F)ˣ,
            sLocalFiniteRestriction v (chart(χ) 0) x =
              ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
          a = (((m : ℝ) * period - t : ℝ) : ℂ) * Complex.I)

/-- Paper: Lemma 7.1.2.2(2), p. 317. The distinct finite pole centers of a unitary character
are separated by an inverse power of the height.
Deviation: This is the quantitative hypothesis proposed for the separate sums in Theorem
7.1.2.3 on #7279. Several places may contribute the same center. -/
def sLocalFinitePolePolynomialSeparation (χ : PontryaginDual Jₛ) : Prop :=
  ∃ c > (0 : ℝ), ∃ d : ℕ, ∀ a b : ℂ, (∃ v : S, sLocalPoleContributes χ (Sum.inr v) a) →
    (∃ w : S, sLocalPoleContributes χ (Sum.inr w) b) → a ≠ b →
      c / (1 + |a.im|) ^ d ≤ ‖b - a‖

/-- Paper: Lemma 7.1.2.2, pp. 316–317. A complex point is a pole of the S-local correcting
factor if and only if at least one place in `InfinitePlace F ⊕ S` contributes it. -/
theorem sLocalPoleContributes_exists_iff (χ : PontryaginDual Jₛ) (a : ℂ) :
    meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ↔
      ∃ v : Places, sLocalPoleContributes χ v a := by
  refine (sLocalRhoFactor_poles_iff χ a).trans ?_
  constructor
  · rintro (⟨w, hw, n, h⟩ | ⟨w, hw, n, h⟩ | ⟨v, m, t, h⟩)
    · exact ⟨Sum.inl w, Or.inl ⟨hw, n, h⟩⟩
    · exact ⟨Sum.inl w, Or.inr ⟨hw, n, h⟩⟩
    · exact ⟨Sum.inr v, m, t, h⟩
  · rintro ⟨w | v, h⟩
    · rcases h with ⟨hw, n, h⟩ | ⟨hw, n, h⟩
      · exact Or.inl ⟨w, hw, n, h⟩
      · exact Or.inr (Or.inl ⟨w, hw, n, h⟩)
    · exact Or.inr (Or.inr ⟨v, h⟩)

/-- Paper: Lemma 7.1.2.2(2), p. 317. At a finite place, the explicit lattice condition agrees
with having a pole of the restricted finite local Tate factor. -/
theorem sLocalPoleContributes_finite_iff_tateFactor (χ : PontryaginDual Jₛ) (v : S) (a : ℂ) :
    sLocalPoleContributes χ (Sum.inr v) a ↔
      meromorphicOrderAt
        (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (chart(χ) z))) a < 0 := by
  obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
  have hψ : ∀ x : (v.val.adicCompletion F)ˣ, ‖sLocalFiniteRestriction v (chart(χ) 0) x‖ = 1 := by
    intro x
    change ‖((χ _ : Circle) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  rw [(h a).2.1]
  exact (sLocalRhoFactor_poles_iff_finite_explicit v.val _ hψ π hπ a).symm

/-- Paper: Lemma 7.1.2.2(1), p. 317. At a real archimedean place, the explicit condition agrees
with having a pole of the restricted infinite local Tate factor. -/
theorem sLocalPoleContributes_real_iff_tateFactor (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsReal) (a : ℂ) :
    sLocalPoleContributes χ (Sum.inl w) a ↔
      meromorphicOrderAt
        (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (chart(χ) z))) a < 0 := by
  rw [(sLocalRhoFactor_poles_iff_real χ w hw a).2.1]
  constructor
  · rintro (⟨_, n, h⟩ | ⟨hc, _⟩)
    · exact ⟨n, h⟩
    · exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr hc)
  · rintro ⟨n, h⟩
    exact Or.inl ⟨hw, n, h⟩

/-- Reconstruction: To count each shared pole once (F88), an assignment chooses one contributing
place in `InfinitePlace F ⊕ S` for every pole of `sLocalRhoFactor (chart(χ) ·)`. -/
def IsValidPoleAssignment (χ : PontryaginDual Jₛ) (assign : ℂ → Places) : Prop :=
  ∀ a : ℂ, meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 →
    sLocalPoleContributes χ (assign a) a

/-- Every unitary S-local character admits a valid pole assignment. -/
theorem exists_isValidPoleAssignment (χ : PontryaginDual Jₛ) :
    ∃ assign : ℂ → Places, IsValidPoleAssignment χ assign := by
  classical
  refine ⟨fun a ↦ if h : ∃ v : Places, sLocalPoleContributes χ v a then h.choose
    else Sum.inl (Classical.arbitrary (InfinitePlace F)), fun a ha ↦ ?_⟩
  have hex : ∃ v : Places, sLocalPoleContributes χ v a :=
    (sLocalPoleContributes_exists_iff χ a).mp ha
  dsimp only
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-! ## Parameterized statement of Theorem 7.1.2.3 -/

open Classical in
/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. The repaired separately summed expansion
parameterized by an explicit pole assignment `assign : ℂ → InfinitePlace F ⊕ S`.
This is a proposition asserting nothing; #7279 asks for which valid assignments, if any, it holds.
Deviation: The open strip `Re z ∈ (-A, 1)` includes zero and the actual archimedean abscissae
(F87); the residue of `(r g)⁻ᶻ Z f z` fixes the Laurent sign and index (F89, I211); the character
contributes its conjugate; shared poles are assigned once according to `assign` (F88).
Reconstruction: The finite outer sum runs over `InfinitePlace F ⊕ S` with the two height ends
escaping independently along `atBot ×ˢ atTop`, matching the bilateral series at each place. -/
def sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor (χ : PontryaginDual Jₛ)
    (A : ℝ) (_hA : 0 < A) (assign : ℂ → Places) : Prop :=
  let Z (f : Tests) (z : ℂ) := sLocalIdelicZFunction f (chart(χ) z)
  let r (g : Jₛ) : ℝ := (normₛ g).val
  let ω := χ.comp (⟨(normₛ).ker.subtype, continuous_subtype_val⟩ : (normₛ).ker →ₜ* Jₛ)
  let θ := sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω
  let poles (h : ℝ × ℝ) := (finite_rectanglePoles
    (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1) (b := 2)
    (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
    (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).toFinset
  let partialSum (v : Places) (h : ℝ × ℝ) (f : Tests) (g : Jₛ) :=
    ∑ a ∈ (poles h).filter (assign · = v),
      star (χ g : ℂ) * complexResidue (fun z ↦ (r g : ℂ) ^ (-z) * Z f z) a
  ∃ L : Places → Tests → Jₛ → ℂ,
    (∀ v f (K : Set Jₛ), IsCompact K →
      TendstoUniformlyOn (fun h g ↦ partialSum v h f g) (L v f) (atBot ×ˢ atTop) K) ∧
    (∀ v (g : Jₛ), r g < 1 → ∀ B : Set Tests, Bornology.IsVonNBounded ℂ B →
      TendstoUniformlyOn (fun h f ↦ partialSum v h f g) (fun f ↦ L v f g) (atBot ×ˢ atTop) B) ∧
    (∀ f, Complex.VerticalIntegrable (Z f) (-A) ∧ ∀ g, r g < 1 →
      ‖θ f g - ∑ v, L v f g‖ ≤
        ((∫ y : ℝ, ‖Z f ((-A : ℝ) + (y : ℂ) * Complex.I)‖) / (2 * Real.pi)) * r g ^ A) ∧
    (∀ B : Set Tests, Bornology.IsVonNBounded ℂ B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ f ∈ B, ∀ g, r g < 1 → ‖θ f g - ∑ v, L v f g‖ ≤ C * r g ^ A)

/-! ## Joint limits, contour totals, and assignment invariance -/

open Classical in
/-- Paper: Theorem 7.1.2.3, p. 322. When the separate place sums converge for any assignment,
summing their limits gives the limit of the joint pole sums along any pair of escaping heights. -/
theorem tendsto_jointPoleSum_of_separatePlaceLimits {ι : Type*} [Fintype ι]
    (poles : ℝ × ℝ → Finset ℂ) (assign : ℂ → ι) (term : ℂ → ℂ) (L : ι → ℂ)
    (hL : ∀ v, Tendsto (fun h ↦ ∑ a ∈ (poles h).filter (assign · = v), term a)
      (atBot ×ˢ atTop) (𝓝 (L v))) {lo hi : ℕ → ℝ}
    (hlo : Tendsto lo atTop atBot) (hhi : Tendsto hi atTop atTop) :
    Tendsto (fun n ↦ ∑ a ∈ poles (lo n, hi n), term a) atTop (𝓝 (∑ v, L v)) := by
  have h := tendsto_finsetSum Finset.univ
    (fun v _ ↦ (hL v).comp (hlo.prodMk hhi))
  exact h.congr fun n ↦ Finset.sum_fiberwise (poles (lo n, hi n)) assign term

open Classical in
/-- Any two assignments for which the separate place sums converge yield the same total sum. -/
theorem sum_separatePlaceLimits_eq_of_assignments {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (poles : ℝ × ℝ → Finset ℂ) (term : ℂ → ℂ)
    (assign₁ : ℂ → ι₁) (L₁ : ι₁ → ℂ)
    (hL₁ : ∀ v, Tendsto (fun h ↦ ∑ a ∈ (poles h).filter (assign₁ · = v), term a)
      (atBot ×ˢ atTop) (𝓝 (L₁ v)))
    (assign₂ : ℂ → ι₂) (L₂ : ι₂ → ℂ)
    (hL₂ : ∀ v, Tendsto (fun h ↦ ∑ a ∈ (poles h).filter (assign₂ · = v), term a)
      (atBot ×ˢ atTop) (𝓝 (L₂ v))) :
    ∑ v, L₁ v = ∑ v, L₂ v := by
  have hhi : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hhi
  exact tendsto_nhds_unique
    (tendsto_jointPoleSum_of_separatePlaceLimits poles assign₁ term L₁ hL₁ hlo hhi)
    (tendsto_jointPoleSum_of_separatePlaceLimits poles assign₂ term L₂ hL₂ hlo hhi)

open Classical in
/-- Paper: Theorem B.3.2.1, p. 606. For the contour shift used on p. 322, if the separate
residue sums converge for any assignment, then their sum equals the normalized difference of
vertical line integrals. -/
theorem sum_separatePlaceLimits_eq_verticalLineIntegral_sub {ι : Type*} [Fintype ι]
    {f Φ : ℂ → ℂ} {a b a' b' σ₁ σ₂ : ℝ} {T : ℤ → ℝ}
    (hT : WitnessesSlowGrowthNearPoles f a b T) (ha : a' < a) (hb : b < b')
    (hΦ : UniformlySchwartzOnStrip Φ a' b') (hσ₁ : a < σ₁) (hσ : σ₁ < σ₂) (hσ₂ : σ₂ < b)
    (hSides : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ),
      let trace := fun y : ℝ ↦ f ((σ : ℂ) + y * Complex.I)
      Continuous trace ∧ ∃ γ > (0 : ℝ), trace =O[comap abs atTop] (fun y : ℝ ↦ |y| ^ γ))
    (hHeights : ∀ k : ℕ, 0 < k → T (-(k : ℤ)) < 0 ∧ 0 < T (k : ℤ))
    (assign : ℂ → ι) (L : ι → ℂ)
    (hL : ∀ v, Tendsto (fun h : ℝ × ℝ ↦ ∑ z ∈
      (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hT.2.1 hσ₁ hσ₂).toFinset.filter
        (assign · = v), complexResidue (fun s ↦ Φ s * f s) z) (atBot ×ˢ atTop) (𝓝 (L v))) :
    ∑ v, L v = (verticalLineIntegral (fun s ↦ Φ s * f s) σ₂ -
      verticalLineIntegral (fun s ↦ Φ s * f s) σ₁) / (2 * (Real.pi : ℂ) * Complex.I) := by
  have hk : ∀ᶠ k : ℕ in atTop, 0 < k := eventually_gt_atTop 0
  have hIndex : Tendsto (fun k : ℕ ↦ (k : ℤ)) atTop (comap abs atTop) := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def, abs_of_nonneg (Int.natCast_nonneg _)] using
      (tendsto_natCast_atTop_atTop (R := ℤ))
  have hLo : Tendsto (fun k : ℕ ↦ T (-(k : ℤ))) atTop atBot := by
    have hNeg : Tendsto (fun k : ℕ ↦ -(k : ℤ)) atTop (comap abs atTop) :=
      tendsto_comap_iff.mpr (by simpa [Function.comp_def] using tendsto_comap_iff.mp hIndex)
    exact (tendsto_neg_atTop_atBot.comp (hT.2.2.2.2.1.comp hNeg)).congr'
      (hk.mono fun k h ↦ neg_eq_iff_eq_neg.mpr (abs_of_neg (hHeights k h).1))
  have hHi : Tendsto (fun k : ℕ ↦ T (k : ℤ)) atTop atTop :=
    (hT.2.2.2.2.1.comp hIndex).congr' (hk.mono fun k h ↦ abs_of_pos (hHeights k h).2)
  exact tendsto_nhds_unique (tendsto_jointPoleSum_of_separatePlaceLimits _ assign _ L hL hLo hHi)
    (tendsto_rectangleResidueSum hT ha hb hΦ hσ₁ hσ hσ₂ hSides hHeights)

/-- Reassigning a finite subset `E ⊆ s` shifts each fiber sum by a constant independent of `s`. -/
private theorem filter_sum_sub_of_subset {ι : Type*} [DecidableEq ι]
    (s E : Finset ℂ) (hEs : E ⊆ s) (assign₁ assign₂ : ℂ → ι)
    (hagree : ∀ a ∈ s, a ∉ E → assign₁ a = assign₂ a) (term : ℂ → ℂ) (v : ι) :
    ∑ a ∈ s.filter (assign₂ · = v), term a =
      (∑ a ∈ s.filter (assign₁ · = v), term a) +
        ((∑ a ∈ E.filter (assign₂ · = v), term a) -
          (∑ a ∈ E.filter (assign₁ · = v), term a)) := by
  classical
  have hsplit (assign : ℂ → ι) :
      ∑ a ∈ s.filter (assign · = v), term a =
        (∑ a ∈ E.filter (assign · = v), term a) +
          (∑ a ∈ (s \ E).filter (assign · = v), term a) := by
    rw [← Finset.sum_union]
    · congr 1
      ext a
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · intro ⟨has, hav⟩
        by_cases haE : a ∈ E
        · exact Or.inl ⟨haE, hav⟩
        · exact Or.inr ⟨⟨has, haE⟩, hav⟩
      · rintro (⟨haE, hav⟩ | ⟨⟨has, _⟩, hav⟩)
        · exact ⟨hEs haE, hav⟩
        · exact ⟨has, hav⟩
    · rw [Finset.disjoint_left]
      intro a ha₁ ha₂
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha₂).1).2 (Finset.mem_filter.mp ha₁).1
  have hsdiff : (s \ E).filter (assign₂ · = v) = (s \ E).filter (assign₁ · = v) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor <;> rintro ⟨⟨has, haE⟩, hav⟩
    · exact ⟨⟨has, haE⟩, (hagree a has haE).trans hav⟩
    · exact ⟨⟨has, haE⟩, (hagree a has haE).symm.trans hav⟩
  rw [hsplit assign₂, hsplit assign₁, hsdiff]
  ring

/-- A finite set of complex numbers lies inside every sufficiently tall horizontal window. -/
private theorem eventually_im_mem_Ioo_of_finset (E : Finset ℂ) :
    ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, ∀ a ∈ E, a.im ∈ Ioo h.1 h.2 := by
  by_cases hE : E.Nonempty
  · let lo : ℝ := (E.image Complex.im).min' (hE.image Complex.im) - 1
    let hi : ℝ := (E.image Complex.im).max' (hE.image Complex.im) + 1
    have hlo : ∀ᶠ x : ℝ in atBot, x ≤ lo := eventually_le_atBot lo
    have hhi : ∀ᶠ y : ℝ in atTop, hi ≤ y := eventually_ge_atTop hi
    filter_upwards [hlo.prod_mk hhi] with h hh a ha
    have him : a.im ∈ E.image Complex.im := Finset.mem_image_of_mem Complex.im ha
    have hmin : (E.image Complex.im).min' (hE.image Complex.im) ≤ a.im :=
      Finset.min'_le _ _ him
    have hmax : a.im ≤ (E.image Complex.im).max' (hE.image Complex.im) :=
      Finset.le_max' _ _ him
    exact ⟨by dsimp [lo] at hh; linarith [hh.1], by dsimp [hi] at hh; linarith [hh.2]⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hE
    subst hE
    exact Eventually.of_forall fun _ _ ha ↦ (Finset.notMem_empty _ ha).elim

/-- Adding a constant function independent of the filter index preserves uniform convergence. -/
private theorem tendstoUniformlyOn_add_const {ι X : Type*} {l : Filter ι} {K : Set X}
    {F G : ι → X → ℂ} {L C : X → ℂ}
    (hF : TendstoUniformlyOn F L l K)
    (heq : ∀ᶠ i in l, ∀ x ∈ K, G i x = F i x + C x) :
    TendstoUniformlyOn G (fun x ↦ L x + C x) l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  filter_upwards [hF ε hε, heq] with i hi he x hx
  rw [he x hx, dist_add_right]
  exact hi x hx

/-- One direction of invariance of `sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor` under
changing `assign` on finitely many strip poles. -/
private theorem separatePlaceExpansionFor_mp_of_finite_diff (χ : PontryaginDual Jₛ)
    (A : ℝ) (hA : 0 < A) (assign₁ assign₂ : ℂ → Places)
    (hfin : {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ∧
      assign₁ a ≠ assign₂ a}.Finite)
    (h₁ : sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  classical
  dsimp only [sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor] at h₁ ⊢
  obtain ⟨L₁, hK₁, hB₁, hrem₁, hBrem₁⟩ := h₁
  let E : Finset ℂ := hfin.toFinset
  let Z (f : Tests) (z : ℂ) := sLocalIdelicZFunction f (chart(χ) z)
  let r (g : Jₛ) : ℝ := (normₛ g).val
  let term (f : Tests) (g : Jₛ) (a : ℂ) : ℂ :=
    star (χ g : ℂ) * complexResidue (fun z ↦ (r g : ℂ) ^ (-z) * Z f z) a
  let poles (h : ℝ × ℝ) := (finite_rectanglePoles
    (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1) (b := 2)
    (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
    (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).toFinset
  let shift (v : Places) (f : Tests) (g : Jₛ) : ℂ :=
    (∑ a ∈ E.filter (assign₂ · = v), term f g a) -
      (∑ a ∈ E.filter (assign₁ · = v), term f g a)
  have hshift_sum (f : Tests) (g : Jₛ) : ∑ v : Places, shift v f g = 0 := by
    simp only [shift, Finset.sum_sub_distrib, Finset.sum_fiberwise, sub_self]
  have hsub : ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, E ⊆ poles h := by
    filter_upwards [eventually_im_mem_Ioo_of_finset E] with h hh a ha
    have haE := hfin.mem_toFinset.mp ha
    exact (finite_rectanglePoles (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1)
      (b := 2) (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
      (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).mem_toFinset.mpr
      ⟨haE.1, hh a ha, haE.2.1⟩
  have hagree (h : ℝ × ℝ) (a : ℂ) (ha : a ∈ poles h) (haE : a ∉ E) :
      assign₁ a = assign₂ a := by
    by_contra hne
    have hap := (finite_rectanglePoles (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1)
      (b := 2) (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
      (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).mem_toFinset.mp ha
    exact haE (hfin.mem_toFinset.mpr ⟨hap.1, hap.2.2, hne⟩)
  have hdiff : ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, ∀ (v : Places) (f : Tests) (g : Jₛ),
      (∑ a ∈ (poles h).filter (assign₂ · = v), term f g a) =
        (∑ a ∈ (poles h).filter (assign₁ · = v), term f g a) + shift v f g := by
    filter_upwards [hsub] with h hEs v f g
    exact filter_sum_sub_of_subset (poles h) E hEs assign₁ assign₂ (hagree h) (term f g) v
  refine ⟨fun v f g ↦ L₁ v f g + shift v f g, ?_, ?_, ?_, ?_⟩
  · intro v f K hK
    exact tendstoUniformlyOn_add_const (hK₁ v f K hK)
      (hdiff.mono fun h hh g _ ↦ hh v f g)
  · intro v g hg B hB
    exact tendstoUniformlyOn_add_const (hB₁ v g hg B hB)
      (hdiff.mono fun h hh f _ ↦ hh v f g)
  · intro f
    refine ⟨(hrem₁ f).1, fun g hg ↦ ?_⟩
    have hsum : (∑ v : Places, (L₁ v f g + shift v f g)) = ∑ v : Places, L₁ v f g := by
      rw [Finset.sum_add_distrib, hshift_sum, add_zero]
    simpa only [hsum] using (hrem₁ f).2 g hg
  · intro B hB
    obtain ⟨C, hC, hbound⟩ := hBrem₁ B hB
    refine ⟨C, hC, fun f hf g hg ↦ ?_⟩
    have hsum : (∑ v : Places, (L₁ v f g + shift v f g)) = ∑ v : Places, L₁ v f g := by
      rw [Finset.sum_add_distrib, hshift_sum, add_zero]
    simpa only [hsum] using hbound f hf g hg

/-- Changing a pole assignment on finitely many strip poles does not affect whether the
separately summed expansion of Theorem 7.1.2.3 holds. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_finite_diff
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A) (assign₁ assign₂ : ℂ → Places)
    (hfin : {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ∧
      assign₁ a ≠ assign₂ a}.Finite) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁ ↔
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  refine ⟨separatePlaceExpansionFor_mp_of_finite_diff χ A hA assign₁ assign₂ hfin, ?_⟩
  have hfin' : {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ∧
      assign₂ a ≠ assign₁ a}.Finite :=
    hfin.subset fun a ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3.symm⟩
  exact separatePlaceExpansionFor_mp_of_finite_diff χ A hA assign₂ assign₁ hfin'

/-! ## Classification of shared poles and assignment independence across distinct primes -/

/-- Only finitely many archimedean poles of `sLocalRhoFactor (chart(χ) ·)` have real part in
`[-A, 1]`. -/
theorem sLocalPoleContributes_archimedean_finite_in_strip (χ : PontryaginDual Jₛ) (A : ℝ) :
    {a : ℂ | a.re ∈ Icc (-A) 1 ∧ ∃ w : InfinitePlace F,
      sLocalPoleContributes χ (Sum.inl w) a}.Finite := by
  have hreal (w : InfinitePlace F) (hw : w.IsReal) :
      {a : ℂ | a.re ∈ Icc (-A) 1 ∧
        let p := (realLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        ∃ n : ℕ, a = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)}.Finite := by
    let p := (realLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
    let N : ℕ := ⌈A + (-p.1).re⌉₊ + 1
    refine ((Finset.range N).finite_toSet.image
      (fun n : ℕ ↦ -p.1 - ((2 * n + p.2.val : ℕ) : ℂ))).subset ?_
    rintro a ⟨ha, n, rfl⟩
    refine ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    have hre : (-p.1 - ((2 * n + p.2.val : ℕ) : ℂ)).re = (-p.1).re - (2 * n + p.2.val : ℝ) := by
      simp
    have hle : (n : ℝ) ≤ A + (-p.1).re := by
      have hp2 : (0 : ℝ) ≤ (p.2.val : ℝ) := Nat.cast_nonneg _
      have h1 : -A ≤ (-p.1).re - (2 * (n : ℝ) + (p.2.val : ℝ)) := by
        have ha1 : -A ≤ (-p.1 - ((2 * n + p.2.val : ℕ) : ℂ)).re := ha.1
        simpa [hre] using ha1
      linarith
    have hceil : (n : ℝ) ≤ (⌈A + (-p.1).re⌉₊ : ℝ) := hle.trans (Nat.le_ceil _)
    have hnat : n ≤ ⌈A + (-p.1).re⌉₊ := by exact_mod_cast hceil
    omega
  have hcomplex (w : InfinitePlace F) (hw : w.IsComplex) :
      {a : ℂ | a.re ∈ Icc (-A) 1 ∧
        let p := (complexLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        ∃ n : ℕ, a = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)}.Finite := by
    let p := (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
    let N : ℕ := ⌈A + (-p.1).re⌉₊ + 1
    refine ((Finset.range N).finite_toSet.image
      (fun n : ℕ ↦ -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ))).subset ?_
    rintro a ⟨ha, n, rfl⟩
    refine ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    have hre : (-p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)).re =
        (-p.1).re - (p.2.natAbs : ℝ) / 2 - (n : ℝ) := by
      simp
    have hle : (n : ℝ) ≤ A + (-p.1).re := by
      have hp2 : (0 : ℝ) ≤ (p.2.natAbs : ℝ) / 2 := by positivity
      have h1 : -A ≤ (-p.1).re - (p.2.natAbs : ℝ) / 2 - (n : ℝ) := by
        have ha1 : -A ≤ (-p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)).re := ha.1
        simpa [hre] using ha1
      linarith
    have hceil : (n : ℝ) ≤ (⌈A + (-p.1).re⌉₊ : ℝ) := hle.trans (Nat.le_ceil _)
    have hnat : n ≤ ⌈A + (-p.1).re⌉₊ := by exact_mod_cast hceil
    omega
  have hunion :
      {a : ℂ | a.re ∈ Icc (-A) 1 ∧ ∃ w : InfinitePlace F,
        sLocalPoleContributes χ (Sum.inl w) a} =
      ⋃ w : InfinitePlace F,
        {a : ℂ | a.re ∈ Icc (-A) 1 ∧ sLocalPoleContributes χ (Sum.inl w) a} := by
    ext a
    simp
  rw [hunion]
  refine Set.finite_iUnion fun w ↦ ?_
  by_cases hw : w.IsReal
  · refine (hreal w hw).subset ?_
    rintro a ⟨ha, h⟩
    rcases h with ⟨_, n, hn⟩ | ⟨hc, _⟩
    · exact ⟨ha, n, hn⟩
    · exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr hc)
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    refine (hcomplex w hc).subset ?_
    rintro a ⟨ha, h⟩
    rcases h with ⟨hr, _⟩ | ⟨_, n, hn⟩
    · exact absurd hr hw
    · exact ⟨ha, n, hn⟩

/-- The absolute norm of a finite place is a positive power of the rational prime below it. -/
private theorem finitePlace_absNorm_eq_prime_pow (v : Primes) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.asIdeal.under ℤ = Ideal.span {(ℓ : ℤ)} ∧
      ∃ f : ℕ, 0 < f ∧ v.asIdeal.absNorm = ℓ ^ f := by
  set P := v.asIdeal.under ℤ
  have hP : P.IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot v.ne_bot
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal P).principal
  have hg' : P = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by rintro rfl; exact hP0 (by rw [hg']; simp)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ hP)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, by rw [hg', Int.span_natAbs], ?_⟩
  have : v.asIdeal.LiesOver P := ⟨rfl⟩
  refine ⟨v.asIdeal.inertiaDeg ℤ, Ideal.inertiaDeg_pos v.asIdeal ℤ, ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg P v.asIdeal, hg', Ideal.absNorm_span_singleton]
  simp

/-- The rationals have a single height-one prime above each nonzero prime ideal of `ℤ`. -/
private theorem rat_prime_unique_above (P : Ideal ℤ) [P.IsMaximal]
    (a b : HeightOneSpectrum (𝓞 ℚ))
    (ha : a.asIdeal.under ℤ = P) (hb : b.asIdeal.under ℤ = P) : a = b := by
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 ℚ)
  rw [RingOfIntegers.rank, Module.finrank_self] at hsum
  have hcard : Fintype.card (P.primesOver (𝓞 ℚ)) ≤ 1 := by
    rw [← hsum, Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have := q.2.1
    have := q.2.2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos ℤ q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  let ea : P.primesOver (𝓞 ℚ) := ⟨a.asIdeal, a.isPrime, ⟨ha.symm⟩⟩
  let eb : P.primesOver (𝓞 ℚ) := ⟨b.asIdeal, b.isPrime, ⟨hb.symm⟩⟩
  exact HeightOneSpectrum.ext (congrArg Subtype.val (Fintype.card_le_one_iff.mp hcard ea eb))

/-- Finite places with multiplicatively dependent absolute norms lie over the same rational
prime. -/
private theorem finitePlace_under_eq_of_absNorm_pow_eq (v w : Primes) {m n : ℕ}
    (hm : 0 < m) (_hn : 0 < n) (h : v.asIdeal.absNorm ^ m = w.asIdeal.absNorm ^ n) :
    v.under (𝓞 ℚ) = w.under (𝓞 ℚ) := by
  obtain ⟨ℓ, hℓ, hvP, f, hf, hvN⟩ := finitePlace_absNorm_eq_prime_pow v
  obtain ⟨ℓ', hℓ', hwP, g, hg, hwN⟩ := finitePlace_absNorm_eq_prime_pow w
  rw [hvN, hwN, ← pow_mul, ← pow_mul] at h
  have hdvd : ℓ ∣ ℓ' := hℓ.dvd_of_dvd_pow (h ▸ dvd_pow_self ℓ (by positivity))
  have hll : ℓ = ℓ' := (Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp hdvd
  subst hll
  have hpr : (Ideal.span {(ℓ : ℤ)}).IsPrime := hvP ▸ Ideal.IsPrime.under ℤ v.asIdeal
  have : (Ideal.span {(ℓ : ℤ)}).IsMaximal := hpr.isMaximal (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hℓ.ne_zero)
  apply rat_prime_unique_above (Ideal.span {(ℓ : ℤ)})
  · change (v.asIdeal.under (𝓞 ℚ)).under ℤ = _
    rw [Ideal.under_under, hvP]
  · change (w.asIdeal.under (𝓞 ℚ)).under ℤ = _
    rw [Ideal.under_under, hwP]

/-- Two poles contributed by the same finite place differ by an integer multiple of its period
times `i`. -/
private theorem sLocalPoleContributes_finite_sub (χ : PontryaginDual Jₛ) (v : S)
    {a₁ a₂ : ℂ} (h₁ : sLocalPoleContributes χ (Sum.inr v) a₁)
    (h₂ : sLocalPoleContributes χ (Sum.inr v) a₂) :
    ∃ k : ℤ, a₂ - a₁ =
      (((k : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨m₁, t₁, ht₁, hchar₁, ha₁⟩ := h₁
  obtain ⟨m₂, t₂, ht₂, hchar₂, ha₂⟩ := h₂
  obtain ⟨π, hπ, -⟩ := sLocalRhoFactor_poles_iff_finite χ v
  have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  set L : ℝ := Real.log (v.val.asIdeal.absNorm : ℝ)
  have hL : 0 < L := Real.log_pos hq
  have hπ0 : 0 < ‖π.val‖ := norm_pos_iff.mpr π.ne_zero
  have hcp (t : ℝ) :
      ((‖π.val‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
        Complex.exp (-((t * L : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hπ0.ne'),
      ← Complex.ofReal_log hπ0.le, hπ, Real.log_inv]
    congr 1
    dsimp only [L]
    push_cast
    ring
  have heq : ((‖π.val‖ : ℝ) : ℂ) ^ ((t₁ : ℂ) * Complex.I) =
      ((‖π.val‖ : ℝ) : ℂ) ^ ((t₂ : ℂ) * Complex.I) :=
    (hchar₁ π).symm.trans (hchar₂ π)
  rw [hcp t₁, hcp t₂, Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  have hreal : -(t₁ * L) = -(t₂ * L) + (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hdiff : t₂ - t₁ = (n : ℝ) * (2 * Real.pi / L) := by
    have hLne : L ≠ 0 := hL.ne'
    field_simp [hLne]
    linarith
  refine ⟨m₂ - m₁ - n, ?_⟩
  rw [ha₁, ha₂]
  have hcoeff : ((m₂ : ℝ) * (2 * Real.pi / L) - t₂) -
      ((m₁ : ℝ) * (2 * Real.pi / L) - t₁) =
      (((m₂ - m₁ - n : ℤ) : ℝ) * (2 * Real.pi / L)) := by
    push_cast
    linarith [hdiff]
  calc
    (((m₂ : ℝ) * (2 * Real.pi / L) - t₂ : ℝ) : ℂ) * Complex.I -
        (((m₁ : ℝ) * (2 * Real.pi / L) - t₁ : ℝ) : ℂ) * Complex.I
      = (((((m₂ : ℝ) * (2 * Real.pi / L) - t₂) -
          ((m₁ : ℝ) * (2 * Real.pi / L) - t₁)) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
    _ = _ := by rw [hcoeff]

/-- Paper: Theorem 7.1.3.2(1), p. 324. Two finite places in `S` over distinct rational primes
contribute at most one pole in common, for every unitary S-local character `χ`. -/
theorem sLocalPoleContributes_finite_common_subsingleton (χ : PontryaginDual Jₛ)
    (v w : S) (hp : v.val.under (𝓞 ℚ) ≠ w.val.under (𝓞 ℚ)) :
    {a : ℂ | sLocalPoleContributes χ (Sum.inr v) a ∧
      sLocalPoleContributes χ (Sum.inr w) a}.Subsingleton := by
  intro a₁ ha₁ a₂ ha₂
  by_contra hne
  obtain ⟨m, hm⟩ := sLocalPoleContributes_finite_sub χ v ha₁.1 ha₂.1
  obtain ⟨n, hn⟩ := sLocalPoleContributes_finite_sub χ w ha₁.2 ha₂.2
  set lv : ℝ := Real.log (v.val.asIdeal.absNorm : ℝ)
  set lw : ℝ := Real.log (w.val.asIdeal.absNorm : ℝ)
  have hqv : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hqw : 1 < (w.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm w.val
  have hlv : 0 < lv := Real.log_pos hqv
  have hlw : 0 < lw := Real.log_pos hqw
  have him : (m : ℝ) * (2 * Real.pi / lv) = (n : ℝ) * (2 * Real.pi / lw) := by
    have := congrArg Complex.im (hm.symm.trans hn)
    simpa only [lv, lw, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero] using this
  have hreal : (m : ℝ) * lw = (n : ℝ) * lv := by
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have : ((m : ℝ) / lv) * (2 * Real.pi) = ((n : ℝ) / lw) * (2 * Real.pi) := by
      linarith [show (m : ℝ) * (2 * Real.pi / lv) = ((m : ℝ) / lv) * (2 * Real.pi) by ring,
        show (n : ℝ) * (2 * Real.pi / lw) = ((n : ℝ) / lw) * (2 * Real.pi) by ring]
    have hdiv : (m : ℝ) / lv = (n : ℝ) / lw := mul_right_cancel₀ h2pi this
    rwa [div_eq_div_iff hlv.ne' hlw.ne'] at hdiv
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    have : a₂ - a₁ = 0 := by simpa using hm
    exact (sub_eq_zero.mp this).symm
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, mul_eq_zero, hlw.ne', or_false] at hreal
    exact hm0 (by exact_mod_cast hreal)
  have habs : (m.natAbs : ℝ) * lw = (n.natAbs : ℝ) * lv := by
    have := congrArg abs hreal
    rw [abs_mul, abs_mul, abs_of_pos hlw, abs_of_pos hlv] at this
    simpa [Int.cast_abs] using this
  have hpow : ((v.val.asIdeal.absNorm ^ n.natAbs : ℕ) : ℝ) =
      ((w.val.asIdeal.absNorm ^ m.natAbs : ℕ) : ℝ) := by
    push_cast
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_pow, Real.log_pow]
    linarith
  exact hp (finitePlace_under_eq_of_absNorm_pow_eq v.val w.val
    (Int.natAbs_pos.mpr hn0) (Int.natAbs_pos.mpr hm0) (by exact_mod_cast hpow))

/-- When `S` contains at most one finite place above each rational prime, only finitely many
strip poles in `Re a ∈ (-A, 1)` are contributed by more than one place. -/
theorem finite_sharedStripPoles_of_injective_under (χ : PontryaginDual Jₛ) (A : ℝ)
    (hinj : Injective (fun v : S ↦ v.val.under (𝓞 ℚ))) :
    {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      ∃ v₁ v₂ : Places, v₁ ≠ v₂ ∧
        sLocalPoleContributes χ v₁ a ∧ sLocalPoleContributes χ v₂ a}.Finite := by
  classical
  have harch := sLocalPoleContributes_archimedean_finite_in_strip χ A
  have hfinPair :
      (⋃ p : S × S, if p.1 ≠ p.2 then
        {a : ℂ | sLocalPoleContributes χ (Sum.inr p.1) a ∧
          sLocalPoleContributes χ (Sum.inr p.2) a}
      else ∅).Finite := by
    refine Set.finite_iUnion fun p ↦ ?_
    split_ifs with hne
    · exact (sLocalPoleContributes_finite_common_subsingleton χ p.1 p.2
        (fun h ↦ hne (hinj h))).finite
    · exact Set.finite_empty
  refine (harch.union hfinPair).subset ?_
  rintro a ⟨hre, v₁, v₂, hne, h₁, h₂⟩
  cases v₁ with
  | inl w =>
    exact Or.inl ⟨⟨hre.1.le, hre.2.le⟩, w, h₁⟩
  | inr v₁ =>
    cases v₂ with
    | inl w =>
      exact Or.inl ⟨⟨hre.1.le, hre.2.le⟩, w, h₂⟩
    | inr v₂ =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨(v₁, v₂), ?_⟩)
      have hvne : v₁ ≠ v₂ := fun h ↦ hne (congrArg Sum.inr h)
      rw [ite_eq_left hvne]
      exact ⟨h₁, h₂⟩

/-- Paper: Theorem 7.1.2.3, pp. 317–323. When `S` contains at most one finite place above each
rational prime, any two valid pole assignments agree outside finitely many strip poles, so the
truth of the separately summed expansion does not depend on the choice of valid assignment. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_injective_under
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hinj : Injective (fun v : S ↦ v.val.under (𝓞 ℚ)))
    (assign₁ assign₂ : ℂ → Places)
    (h₁ : IsValidPoleAssignment χ assign₁) (h₂ : IsValidPoleAssignment χ assign₂) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁ ↔
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  apply sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_finite_diff χ A hA
  refine (finite_sharedStripPoles_of_injective_under χ A hinj).subset ?_
  rintro a ⟨hre, hord, hne⟩
  exact ⟨hre, assign₁ a, assign₂ a, hne, h₁ a hord, h₂ a hord⟩

/-- Over `ℚ`, every finite set `S` has at most one finite place per rational prime, so the
repaired separately summed expansion of Theorem 7.1.2.3 has the same truth value for every valid
pole assignment. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_rat_iff
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (χ : PontryaginDual (SIdeleQuotient ℚ S)) (A : ℝ) (hA : 0 < A)
    (assign₁ assign₂ : ℂ → InfinitePlace ℚ ⊕ S)
    (h₁ : IsValidPoleAssignment χ assign₁) (h₂ : IsValidPoleAssignment χ assign₂) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁ ↔
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  refine sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_injective_under
    χ A hA ?_ assign₁ assign₂ h₁ h₂
  intro v w hvw
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  have h := congrArg HeightOneSpectrum.asIdeal hvw
  change v.val.asIdeal.comap (RingHom.id (𝓞 ℚ)) = w.val.asIdeal.comap (RingHom.id (𝓞 ℚ)) at h
  simpa using h

/-! ## Uniform convergence for every assignment under a summable majorant -/

open Classical in
/-- If the residue terms at the strip poles are bounded uniformly on `K` by a summable
nonnegative majorant `M`, then for every assignment `assign`, the separate place partial sums
converge uniformly on `K` along `atBot ×ˢ atTop` to the unconditional sum over each fiber. -/
theorem tendstoUniformlyOn_separatePlacePartialSum_of_summable_bound {ι X : Type*}
    {f : ℂ → ℂ} {a b σ₁ σ₂ : ℝ} (hf : MeromorphicOn f (Complex.re ⁻¹' Ioo a b))
    (hσ₁ : a < σ₁) (hσ₂ : σ₂ < b)
    (assign : ℂ → ι) (term : ℂ → X → ℂ) (K : Set X)
    (M : {z : ℂ // z.re ∈ Ioo σ₁ σ₂ ∧ meromorphicOrderAt f z < 0} → ℝ)
    (hM0 : ∀ z, 0 ≤ M z) (hM : Summable M)
    (hbound : ∀ z, ∀ x ∈ K, ‖term z.val x‖ ≤ M z) (v : ι) :
    let stripPoles := {z : ℂ // z.re ∈ Ioo σ₁ σ₂ ∧ meromorphicOrderAt f z < 0}
    let rectPoles (h : ℝ × ℝ) := (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2)
      hf hσ₁ hσ₂).toFinset
    let partialSum (h : ℝ × ℝ) (x : X) := ∑ z ∈ (rectPoles h).filter (assign · = v), term z x
    let limit (x : X) := ∑' z : stripPoles, if assign z.val = v then term z.val x else 0
    TendstoUniformlyOn partialSum limit (atBot ×ˢ atTop) K := by
  intro stripPoles rectPoles partialSum limit
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hhas : Tendsto (fun s : Finset stripPoles ↦ ∑ b ∈ s, M b) atTop (𝓝 (∑' b, M b)) :=
    hM.hasSum
  rw [Metric.tendsto_atTop] at hhas
  obtain ⟨s₀, hs₀⟩ := hhas (ε / 2) (half_pos hε)
  have htsum_tail : ∀ s : Finset stripPoles, s₀ ⊆ s →
      (∑' z : stripPoles, if z ∉ s then M z else 0) < ε := by
    intro s hs
    have hfin : Summable (fun z : stripPoles ↦ if z ∈ s then M z else 0) :=
      summable_of_ne_finset_zero (s := s) fun z hz ↦ ite_eq_right hz
    have hcompl : Summable (fun z : stripPoles ↦ if z ∉ s then M z else 0) :=
      hM.of_nonneg_of_le (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
        (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
    have hsplit : (∑' z : stripPoles, if z ∈ s then M z else 0) +
        (∑' z : stripPoles, if z ∉ s then M z else 0) = ∑' z : stripPoles, M z := by
      rw [← hfin.tsum_add hcompl]
      congr 1
      ext z
      by_cases hz : z ∈ s <;> simp [hz]
    have hsum_eq : (∑' z : stripPoles, if z ∈ s then M z else 0) = ∑ z ∈ s, M z := by
      rw [tsum_eq_sum (s := s) (fun z hz ↦ ite_eq_right hz)]
      exact Finset.sum_congr rfl fun z hz ↦ ite_eq_left hz
    have hdist := hs₀ s hs
    rw [Real.dist_eq] at hdist
    have hle : (∑ z ∈ s, M z) ≤ ∑' z : stripPoles, M z :=
      hM.sum_le_tsum s fun z _ ↦ hM0 z
    have hdiff : (∑' z : stripPoles, M z) - (∑ z ∈ s, M z) < ε / 2 := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at hdist
      exact hdist
    linarith
  let E : Finset ℂ := s₀.image Subtype.val
  filter_upwards [eventually_im_mem_Ioo_of_finset E] with h hh x hx
  let emb : ↥(rectPoles h) ↪ stripPoles :=
    ⟨fun z ↦ ⟨z.val, by
      have hz := (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hf hσ₁ hσ₂).mem_toFinset.mp z.property
      exact ⟨hz.1, hz.2.2⟩⟩,
      fun a b hab ↦ Subtype.ext (Subtype.mk.inj hab)⟩
  let s : Finset stripPoles := (rectPoles h).attach.map emb
  have hs_sub : s₀ ⊆ s := by
    intro z hz
    have hzE : z.val ∈ E := Finset.mem_image_of_mem Subtype.val hz
    have hzrect : z.val ∈ rectPoles h :=
      (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hf hσ₁ hσ₂).mem_toFinset.mpr
        ⟨z.property.1, hh z.val hzE, z.property.2⟩
    refine Finset.mem_map.mpr ⟨⟨z.val, hzrect⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl
  let g (z : stripPoles) : ℂ := if assign z.val = v then term z.val x else 0
  have hg_norm (z : stripPoles) : ‖g z‖ ≤ M z := by
    dsimp only [g]
    split_ifs
    · exact hbound z x hx
    · rw [norm_zero]; exact hM0 z
  have hg_summable : Summable g := Summable.of_norm_bounded hM hg_norm
  have hpart : partialSum h x = ∑ z ∈ s, g z := by
    dsimp only [partialSum, s, g]
    rw [Finset.sum_map]
    have hcongr : ∀ z : ↥(rectPoles h),
        (if assign (emb z).val = v then term (emb z).val x else 0) =
          (if assign z.val = v then term z.val x else 0) := fun _ ↦ rfl
    simp_rw [hcongr]
    rw [Finset.sum_attach (rectPoles h) (fun z ↦ if assign z = v then term z x else 0),
      ← Finset.sum_filter]
  have hfin_g : Summable (fun z : stripPoles ↦ if z ∈ s then g z else 0) :=
    summable_of_ne_finset_zero (s := s) fun z hz ↦ ite_eq_right hz
  have hcompl_g : Summable (fun z : stripPoles ↦ if z ∉ s then g z else 0) :=
    Summable.of_norm_bounded hM fun z ↦ by
      by_cases hz : z ∈ s <;> simp [hz, hg_norm z, hM0 z]
  have hsplit_g : limit x = (∑ z ∈ s, g z) + ∑' z : stripPoles, if z ∉ s then g z else 0 := by
    change (∑' z : stripPoles, g z) = _
    have hsum_eq : (∑' z : stripPoles, if z ∈ s then g z else 0) = ∑ z ∈ s, g z := by
      rw [tsum_eq_sum (s := s) (fun z hz ↦ ite_eq_right hz)]
      exact Finset.sum_congr rfl fun z hz ↦ ite_eq_left hz
    rw [← hsum_eq, ← hfin_g.tsum_add hcompl_g]
    congr 1
    ext z
    by_cases hz : z ∈ s <;> simp [hz]
  have hcompl_M : Summable (fun z : stripPoles ↦ if z ∉ s then M z else 0) :=
    hM.of_nonneg_of_le (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
      (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
  rw [dist_eq_norm, hpart, hsplit_g, add_sub_cancel_left]
  calc
    ‖∑' z : stripPoles, if z ∉ s then g z else 0‖
      ≤ ∑' z : stripPoles, ‖if z ∉ s then g z else 0‖ := norm_tsum_le_tsum_norm hcompl_g.norm
    _ ≤ ∑' z : stripPoles, if z ∉ s then M z else 0 := by
        refine hcompl_g.norm.tsum_le_tsum (fun z ↦ ?_) hcompl_M
        by_cases hz : z ∈ s <;> simp [hz, hg_norm z]
    _ < ε := htsum_tail s hs_sub

/-! ## Uniform pole discreteness over a single rational prime -/

/-- A finite union of translates of a single periodic lattice `ω · ℤ` in `ℝ` is uniformly
discrete. -/
private theorem uniformly_discrete_finite_union_periodic {ι : Type*} [Fintype ι]
    {ω : ℝ} (hω : 0 < ω) (shift : ι → ℝ) :
    ∃ δ > (0 : ℝ), ∀ (i j : ι) (m n : ℤ),
      ((m : ℝ) * ω + shift i) ≠ ((n : ℝ) * ω + shift j) →
      δ ≤ |((m : ℝ) * ω + shift i) - ((n : ℝ) * ω + shift j)| := by
  classical
  let rem (p : ι × ι) : ℝ :=
    (shift p.1 - shift p.2) - (⌊(shift p.1 - shift p.2) / ω⌋ : ℝ) * ω
  have hrem_mem (p : ι × ι) : rem p ∈ Ico 0 ω := by
    have hfl := Int.floor_le ((shift p.1 - shift p.2) / ω)
    have hlt := Int.lt_floor_add_one ((shift p.1 - shift p.2) / ω)
    constructor
    · dsimp [rem]
      have := (le_div_iff₀ hω).mp hfl
      linarith
    · dsimp [rem]
      have := (div_lt_iff₀ hω).mp hlt
      linarith
  let gap (p : ι × ι) : ℝ := if rem p = 0 then ω else min (rem p) (ω - rem p)
  have hgap_pos (p : ι × ι) : 0 < gap p := by
    dsimp [gap]
    split_ifs with h0
    · exact hω
    · have hm := hrem_mem p
      exact lt_min (lt_of_le_of_ne hm.1 (Ne.symm h0)) (sub_pos.mpr hm.2)
  let G : Finset ℝ := insert ω (Finset.univ.image gap)
  have hGne : G.Nonempty := ⟨ω, Finset.mem_insert_self _ _⟩
  let δ : ℝ := G.min' hGne
  have hδ_pos : 0 < δ := by
    rw [Finset.lt_min'_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hω
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx'
      exact hgap_pos p
  refine ⟨δ, hδ_pos, fun i j m n hne ↦ ?_⟩
  let k : ℤ := m - n + ⌊(shift i - shift j) / ω⌋
  have hdiff : ((m : ℝ) * ω + shift i) - ((n : ℝ) * ω + shift j) = (k : ℝ) * ω + rem (i, j) := by
    dsimp [k, rem]
    push_cast
    ring
  rw [hdiff]
  by_cases h0 : rem (i, j) = 0
  · rw [h0, add_zero]
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hne
      have hsub0 : ((m : ℝ) * ω + shift i) - ((n : ℝ) * ω + shift j) = 0 := by
        rw [hdiff, hk0, h0]
        simp
      exact sub_eq_zero.mp hsub0
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    have hδw : δ ≤ ω := Finset.min'_le G ω (Finset.mem_insert_self _ _)
    rw [abs_mul, abs_of_pos hω]
    nlinarith
  · have hδg : δ ≤ min (rem (i, j)) (ω - rem (i, j)) := by
      have hmem : gap (i, j) ∈ G :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem gap (Finset.mem_univ _))
      have hle := Finset.min'_le G (gap (i, j)) hmem
      simpa [gap, h0] using hle
    have hm := hrem_mem (i, j)
    have hrem_pos : 0 < rem (i, j) := lt_of_le_of_ne hm.1 (Ne.symm h0)
    have hgap_le : min (rem (i, j)) (ω - rem (i, j)) ≤ |(k : ℝ) * ω + rem (i, j)| := by
      by_cases hk : 0 ≤ k
      · have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hpos : 0 ≤ (k : ℝ) * ω + rem (i, j) := by nlinarith
        rw [abs_of_nonneg hpos]
        exact (min_le_left _ _).trans (by nlinarith)
      · have hk' : (k : ℝ) ≤ -1 := by
          have : k ≤ -1 := by omega
          exact_mod_cast this
        have hneg : (k : ℝ) * ω + rem (i, j) ≤ 0 := by nlinarith [hm.2]
        rw [abs_of_nonpos hneg]
        exact (min_le_right _ _).trans (by nlinarith)
    exact hδg.trans hgap_le

/-- Adding a finite set to a uniformly discrete set in `ℂ` preserves uniform discreteness. -/
private theorem uniformly_discrete_union_finite {A B : Set ℂ}
    (hA : A.Finite) (hB : ∃ δ > (0 : ℝ), ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ ‖x - y‖) :
    ∃ δ > (0 : ℝ), ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, x ≠ y → δ ≤ ‖x - y‖ := by
  classical
  obtain ⟨δB, hδB, hBsep⟩ := hB
  let AF : Finset ℂ := hA.toFinset
  have hcross (a : ℂ) : ∃ d > (0 : ℝ), ∀ b ∈ B, a ≠ b → d ≤ ‖a - b‖ := by
    by_cases hnear : ∃ b ∈ B, ‖a - b‖ < δB / 2
    · obtain ⟨b₀, hb₀, hlt⟩ := hnear
      by_cases hab : a = b₀
      · subst hab
        refine ⟨δB, hδB, fun b hb hne ↦ hBsep a hb₀ b hb hne⟩
      · refine ⟨min ‖a - b₀‖ (δB / 2), lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr hab))
            (half_pos hδB), fun b hb hne ↦ ?_⟩
        by_cases hbb : b = b₀
        · subst hbb; exact min_le_left _ _
        · have htri := hBsep b₀ hb₀ b hb (Ne.symm hbb)
          have hsub : ‖b₀ - b‖ ≤ ‖a - b₀‖ + ‖a - b‖ := by
            calc ‖b₀ - b‖ = ‖(b₀ - a) + (a - b)‖ := by ring_nf
              _ ≤ ‖b₀ - a‖ + ‖a - b‖ := norm_add_le _ _
              _ = ‖a - b₀‖ + ‖a - b‖ := by rw [norm_sub_rev]
          exact (min_le_right _ _).trans (by linarith)
    · push Not at hnear
      exact ⟨δB / 2, half_pos hδB, fun b hb _ ↦ hnear b hb⟩
  choose dA hdA hdA_le using hcross
  let pairDists : Finset ℝ :=
    ((AF ×ˢ AF).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ ‖p.1 - p.2‖)
  let crossDists : Finset ℝ := AF.image dA
  let allDists : Finset ℝ := insert δB (pairDists ∪ crossDists)
  have hallNe : allDists.Nonempty := ⟨δB, Finset.mem_insert_self _ _⟩
  let δ : ℝ := allDists.min' hallNe
  have hδ_pos : 0 < δ := by
    rw [Finset.lt_min'_iff]
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · exact hδB
    · rcases Finset.mem_union.mp hr' with hp | hc
      · obtain ⟨p, hp', rfl⟩ := Finset.mem_image.mp hp
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp').2)
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
        exact hdA a
  refine ⟨δ, hδ_pos, fun x hx y hy hne ↦ ?_⟩
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · have hmem : ‖x - y‖ ∈ allDists :=
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨hA.mem_toFinset.mpr hxA, hA.mem_toFinset.mpr hyA⟩, hne⟩, rfl⟩))
    exact Finset.min'_le _ _ hmem
  · have hmem : dA x ∈ allDists :=
      Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem dA (hA.mem_toFinset.mpr hxA)))
    exact (Finset.min'_le _ _ hmem).trans (hdA_le x y hyB hne)
  · have hmem : dA y ∈ allDists :=
      Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem dA (hA.mem_toFinset.mpr hyA)))
    rw [norm_sub_rev]
    exact (Finset.min'_le _ _ hmem).trans (hdA_le y x hxB hne.symm)
  · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (hBsep x hxB y hyB hne)

/-- Paper: Theorem 7.1.2.3, pp. 317–323. If every finite place in `S` lies over the same rational
prime (including `S = ∅`, a single finite place, or any single-prime fiber `S_p`), then all poles
of `sLocalRhoFactor (chart(χ) ·)` in `Re a ∈ [-A, 1]` are uniformly discrete, for every unitary
S-local character `χ` (including characters of infinite order). -/
theorem sLocalStripPoles_uniformly_discrete_of_same_prime (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    let P := {a : ℂ | a.re ∈ Icc (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0}
    ∃ δ > (0 : ℝ), ∀ a ∈ P, ∀ b ∈ P, a ≠ b → δ ≤ ‖a - b‖ := by
  classical
  intro P
  let P_arch : Set ℂ := {a : ℂ | a.re ∈ Icc (-A) 1 ∧
    ∃ w : InfinitePlace F, sLocalPoleContributes χ (Sum.inl w) a}
  let P_fin : Set ℂ := {a : ℂ | ∃ v : S, sLocalPoleContributes χ (Sum.inr v) a}
  have hPsub : P ⊆ P_arch ∪ P_fin := by
    intro a ⟨hre, hord⟩
    obtain ⟨w | v, hv⟩ := (sLocalPoleContributes_exists_iff χ a).mp hord
    · exact Or.inl ⟨hre, w, hv⟩
    · exact Or.inr ⟨v, hv⟩
  have hfin_disc : ∃ δ > (0 : ℝ), ∀ a ∈ P_fin, ∀ b ∈ P_fin, a ≠ b → δ ≤ ‖a - b‖ := by
    by_cases hSne : S.Nonempty
    · let v₀ : S := ⟨hSne.choose, hSne.choose_spec⟩
      obtain ⟨ℓ, hℓ, hv₀P, _, _, _⟩ := finitePlace_absNorm_eq_prime_pow v₀.val
      have hℓ_gt : (1 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.one_lt
      have hlogℓ : 0 < Real.log (ℓ : ℝ) := Real.log_pos hℓ_gt
      have hf_exists (v : S) : ∃ f : ℕ, 0 < f ∧ v.val.asIdeal.absNorm = ℓ ^ f := by
        obtain ⟨ℓ', hℓ', hvP, f, hf, hvN⟩ := finitePlace_absNorm_eq_prime_pow v.val
        have hunder : v.val.asIdeal.under ℤ = v₀.val.asIdeal.under ℤ := by
          have h := congrArg (fun p : HeightOneSpectrum (𝓞 ℚ) ↦ p.asIdeal.under ℤ) (hsame v v₀)
          simpa [HeightOneSpectrum.under, Ideal.under_under] using h
        have hspan : Ideal.span {(ℓ' : ℤ)} = Ideal.span {(ℓ : ℤ)} := by
          rw [← hvP, hunder, hv₀P]
        have hdvd₁ : (ℓ : ℤ) ∣ (ℓ' : ℤ) :=
          Ideal.mem_span_singleton.mp (hspan ▸ Ideal.subset_span (Set.mem_singleton _))
        have hll : ℓ' = ℓ := (Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp (Int.natCast_dvd_natCast.mp hdvd₁) |>.symm
        subst hll
        exact ⟨f, hf, hvN⟩
      choose deg hdeg_pos hdeg_eq using hf_exists
      let L : ℕ := ∏ v : S, deg v
      have hL_pos : 0 < L := Finset.prod_pos fun v _ ↦ hdeg_pos v
      let ω : ℝ := 2 * Real.pi / ((L : ℝ) * Real.log (ℓ : ℝ))
      have hω_pos : 0 < ω := by positivity
      let shift (v : S) : ℝ :=
        if h : ∃ a : ℂ, sLocalPoleContributes χ (Sum.inr v) a then -h.choose_spec.choose_spec.choose
        else 0
      obtain ⟨δ, hδ, hsep⟩ := uniformly_discrete_finite_union_periodic hω_pos shift
      refine ⟨δ, hδ, fun a ha b hb hne ↦ ?_⟩
      have hcoord (z : ℂ) (hz : z ∈ P_fin) :
          ∃ (v : S) (k : ℤ), z = (((k : ℝ) * ω + shift v : ℝ) : ℂ) * Complex.I := by
        obtain ⟨v, hv⟩ := hz
        have hex : ∃ a : ℂ, sLocalPoleContributes χ (Sum.inr v) a := ⟨z, hv⟩
        let a₀ : ℂ := hex.choose
        have ha₀ : sLocalPoleContributes χ (Sum.inr v) a₀ := hex.choose_spec
        let m₀ : ℤ := ha₀.choose
        let t₀ : ℝ := ha₀.choose_spec.choose
        have ht₀_spec := ha₀.choose_spec.choose_spec
        have hshift_eq : shift v = -t₀ := dite_eq_left hex
        obtain ⟨d, hd⟩ := sLocalPoleContributes_finite_sub χ v ha₀ hv
        have hdvd : deg v ∣ L := Finset.dvd_prod_of_mem deg (Finset.mem_univ v)
        obtain ⟨q, hq⟩ := hdvd
        have hperiod : 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ) = (q : ℝ) * ω := by
          dsimp [ω]
          rw [hdeg_eq v, Nat.cast_pow, Real.log_pow, hq]
          have hdeg0 : (deg v : ℝ) ≠ 0 := by exact_mod_cast (hdeg_pos v).ne'
          have hq0 : (q : ℝ) ≠ 0 := by
            have : q ≠ 0 := by rintro rfl; simp at hq; omega
            exact_mod_cast this
          have hlog0 : Real.log (ℓ : ℝ) ≠ 0 := hlogℓ.ne'
          push_cast
          field_simp [hdeg0, hq0, hlog0]
        refine ⟨v, (m₀ + d) * (q : ℤ), ?_⟩
        have ha₀_eq :
            a₀ = (((m₀ : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) - t₀ : ℝ) : ℂ) *
              Complex.I := ht₀_spec.2.2
        have hz_eq : z = a₀ + (z - a₀) := by ring
        rw [hz_eq, hd, ha₀_eq, hperiod, hshift_eq]
        push_cast
        ring
      obtain ⟨v, k₁, rfl⟩ := hcoord a ha
      obtain ⟨w, k₂, rfl⟩ := hcoord b hb
      have hne' : (k₁ : ℝ) * ω + shift v ≠ (k₂ : ℝ) * ω + shift w := by
        intro heq
        apply hne
        rw [heq]
      have hnorm : ‖(((k₁ : ℝ) * ω + shift v : ℝ) : ℂ) * Complex.I -
          (((k₂ : ℝ) * ω + shift w : ℝ) : ℂ) * Complex.I‖ =
          |((k₁ : ℝ) * ω + shift v) - ((k₂ : ℝ) * ω + shift w)| := by
        rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      exact hsep v w k₁ k₂ hne'
    · refine ⟨1, zero_lt_one, fun a ha _ _ _ ↦ ?_⟩
      obtain ⟨v, _⟩ := ha
      exact (hSne ⟨v.val, v.property⟩).elim
  obtain ⟨δ, hδ, hsep⟩ :=
    uniformly_discrete_union_finite (sLocalPoleContributes_archimedean_finite_in_strip χ A) hfin_disc
  exact ⟨δ, hδ, fun a ha b hb hne ↦ hsep a (hPsub ha) b (hPsub hb) hne⟩

/-! ## Exact arithmetic criterion on a pole lattice (#7279) -/

/-- The shifted inverse-square sequence `(1 + |m|)⁻²` is summable over `ℤ`. -/
private theorem summable_inv_one_add_abs_sq_int :
    Summable (fun m : ℤ ↦ ((1 + |(m : ℝ)|) ^ 2)⁻¹) := by
  have hnat : Summable (fun n : ℕ ↦ ((1 + (n : ℝ)) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num)).comp_injective
      Nat.succ_injective
    refine h.congr fun n ↦ ?_
    simp [add_comm]
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · exact hnat.congr fun n ↦ by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  · exact hnat.congr fun n ↦ by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]

open Classical in
/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323, and the Gaussian-field obstruction in #7279.
For any sequence of complex denominators `D : ℤ → ℂ`, the quotients `b m / D m` (with division
by zero totalized to zero) are summable for every rapidly decreasing sequence `b : ℤ → ℂ` if and
only if `D` satisfies an inverse-polynomial lower bound on its nonzero entries. -/
theorem rapidDecay_div_summable_iff_polyLowerBound (D : ℤ → ℂ) :
    (∀ b : ℤ → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ m : ℤ, (1 + |(m : ℝ)|) ^ k * ‖b m‖ ≤ C) →
      Summable (fun m : ℤ ↦ b m / D m)) ↔
    ∃ (c : ℝ) (d : ℕ), 0 < c ∧ ∀ m : ℤ, D m ≠ 0 → c / (1 + |(m : ℝ)|) ^ d ≤ ‖D m‖ := by
  constructor
  · intro hsum
    by_contra hno
    have hstep : ∀ (n M : ℕ), ∃ m : ℤ, M < m.natAbs ∧ D m ≠ 0 ∧
        ‖D m‖ < 1 / (1 + |(m : ℝ)|) ^ n := by
      intro n M
      by_contra hnone
      push Not at hnone
      let box : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun m ↦ D m ≠ 0)
      let norms : Finset ℝ := insert (1 : ℝ) (box.image (fun m ↦ ‖D m‖))
      have hnormsNe : norms.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
      let c : ℝ := norms.min' hnormsNe
      have hc_pos : 0 < c := by
        dsimp only [c]
        rw [Finset.lt_min'_iff]
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr'
        · exact zero_lt_one
        · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hr'
          exact norm_pos_iff.mpr (Finset.mem_filter.mp hm).2
      have hc_le1 : c ≤ 1 := Finset.min'_le norms 1 (Finset.mem_insert_self _ _)
      apply hno
      refine ⟨c, n, hc_pos, fun m hm ↦ ?_⟩
      by_cases hM : M < m.natAbs
      · exact (div_le_div_of_nonneg_right hc_le1 (by positivity)).trans (hnone m hM hm)
      · have hm_box : m ∈ box := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_, hm⟩
          have : m.natAbs ≤ M := not_lt.mp hM
          omega
        have hc_leD : c ≤ ‖D m‖ :=
          Finset.min'_le norms ‖D m‖
            (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun m ↦ ‖D m‖) hm_box))
        have hpow_ge : (1 : ℝ) ≤ (1 + |(m : ℝ)|) ^ n :=
          one_le_pow₀ (by linarith [abs_nonneg (m : ℝ)])
        exact (div_le_self hc_pos.le hpow_ge).trans hc_leD
    choose pick hpick_gt hpick_ne hpick_lt using hstep
    let seq : ℕ → ℤ := Nat.rec (pick 0 0) (fun j prev ↦ pick (j + 1) prev.natAbs)
    have hseq_ne (j : ℕ) : D (seq j) ≠ 0 := by
      cases j with
      | zero => exact hpick_ne 0 0
      | succ j => exact hpick_ne (j + 1) (seq j).natAbs
    have hseq_lt (j : ℕ) : ‖D (seq j)‖ < 1 / (1 + |(Int.cast (seq j) : ℝ)|) ^ j := by
      cases j with
      | zero => exact hpick_lt 0 0
      | succ j => exact hpick_lt (j + 1) (seq j).natAbs
    have hseq_mono : StrictMono (fun j : ℕ ↦ (seq j).natAbs) := by
      refine strictMono_nat_of_lt_succ fun j ↦ ?_
      exact hpick_gt (j + 1) (seq j).natAbs
    have hseq_inj : Injective seq := fun i j hij ↦
      hseq_mono.injective (congrArg Int.natAbs hij)
    let b : ℤ → ℂ := Set.indicator (Set.range seq) D
    have hb_at (j : ℕ) : b (seq j) = D (seq j) :=
      Set.indicator_of_mem (Set.mem_range_self j) D
    have hb_rapid : ∀ k : ℕ, ∃ C : ℝ, ∀ m : ℤ, (1 + |(m : ℝ)|) ^ k * ‖b m‖ ≤ C := by
      intro k
      let C₀ : ℝ := ∑ j ∈ Finset.range k, (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖
      refine ⟨1 + C₀, fun m ↦ ?_⟩
      have hC₀_nn : 0 ≤ C₀ := Finset.sum_nonneg fun j _ ↦ by positivity
      rcases Classical.em (m ∈ Set.range seq) with ⟨j, rfl⟩ | hex
      · rw [hb_at j]
        by_cases hjk : j < k
        · have hterm : (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖ ≤ C₀ :=
            Finset.single_le_sum (f := fun i ↦ (1 + |(Int.cast (seq i) : ℝ)|) ^ k * ‖D (seq i)‖)
              (fun i _ ↦ by positivity) (Finset.mem_range.mpr hjk)
          linarith
        · have hkj : k ≤ j := not_lt.mp hjk
          have hbase : (1 : ℝ) ≤ 1 + |(Int.cast (seq j) : ℝ)| := by
            linarith [abs_nonneg (Int.cast (seq j) : ℝ)]
          have hpow : (1 + |(Int.cast (seq j) : ℝ)|) ^ k ≤ (1 + |(Int.cast (seq j) : ℝ)|) ^ j :=
            pow_le_pow_right₀ hbase hkj
          have hle1 : (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖ ≤ 1 := by
            calc
              (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖
                ≤ (1 + |(Int.cast (seq j) : ℝ)|) ^ j * (1 / (1 + |(Int.cast (seq j) : ℝ)|) ^ j) :=
                  mul_le_mul hpow (hseq_lt j).le (norm_nonneg _) (by positivity)
              _ = 1 := by
                  have hpos : (0 : ℝ) < (1 + |(Int.cast (seq j) : ℝ)|) ^ j := by positivity
                  field_simp [hpos.ne']
          linarith
      · have hb0 : b m = 0 := Set.indicator_of_notMem hex D
        rw [hb0, norm_zero, mul_zero]
        linarith
    have hs : Summable (fun m : ℤ ↦ b m / D m) := hsum b hb_rapid
    have hcomp : Tendsto (fun j : ℕ ↦ b (seq j) / D (seq j)) atTop (𝓝 0) :=
      hs.tendsto_cofinite_zero.comp (Nat.cofinite_eq_atTop ▸ hseq_inj.tendsto_cofinite)
    have hone : Tendsto (fun j : ℕ ↦ b (seq j) / D (seq j)) atTop (𝓝 1) :=
      tendsto_const_nhds.congr fun j ↦ (by rw [hb_at j, div_self (hseq_ne j)] : (1 : ℂ) = _)
    exact one_ne_zero (tendsto_nhds_unique hone hcomp)
  · rintro ⟨c, d, hc, hD⟩ b hb
    obtain ⟨C, hC⟩ := hb (d + 2)
    have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg (b 0))).trans (hC 0)
    refine Summable.of_norm_bounded (summable_inv_one_add_abs_sq_int.mul_left (C / c)) fun m ↦ ?_
    by_cases hm : D m = 0
    · rw [hm, div_zero, norm_zero]
      positivity
    · have hbase : (0 : ℝ) < 1 + |(m : ℝ)| := by linarith [abs_nonneg (m : ℝ)]
      have hDm : c / (1 + |(m : ℝ)|) ^ d ≤ ‖D m‖ := hD m hm
      have hDm_pos : 0 < ‖D m‖ := norm_pos_iff.mpr hm
      have hbm : ‖b m‖ ≤ C / (1 + |(m : ℝ)|) ^ (d + 2) :=
        (le_div_iff₀ (by positivity)).mpr (by rw [mul_comm]; exact hC m)
      rw [norm_div]
      calc
        ‖b m‖ / ‖D m‖
          ≤ (C / (1 + |(m : ℝ)|) ^ (d + 2)) / (c / (1 + |(m : ℝ)|) ^ d) :=
            div_le_div₀ (by positivity) hbm (by positivity) hDm
        _ = (C / c) * ((1 + |(m : ℝ)|) ^ 2)⁻¹ := by
            rw [pow_add]
            field_simp [hc.ne', hbase.ne']

/-! ## Separate place sums for a single residue characteristic -/

section

open scoped Classical

/-- Paper: Lemma 7.1.2.2, pp. 316–317. At a finite place of norm `p ^ f`, the pole
condition depends only on `exp (log p * a)`. The allowed phases are the `f`-th roots
of the character value on a uniformizer at an unramified place and are empty at a
ramified place.
Deviation: The phase is taken with the sign dictated by the shifted Euler factor. -/
theorem sLocalPoleContributes_finite_phase_finset (χ : PontryaginDual Jₛ) (v : S)
    {p f : ℕ} (hf : 0 < f) (hN : v.val.asIdeal.absNorm = p ^ f) :
    ∃ Q : Finset ℂ, ∀ a : ℂ, sLocalPoleContributes χ (Sum.inr v) a ↔
      Complex.exp ((Real.log (p : ℝ) : ℂ) * a) ∈ Q := by
  classical
  obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
  let ψ := sLocalFiniteRestriction v (chart(χ) 0)
  let U := ∀ u : (v.val.adicCompletionIntegers F)ˣ,
    ψ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1
  let z (a : ℂ) := Complex.exp ((Real.log (p : ℝ) : ℂ) * a)
  have hpow (a : ℂ) : ((‖π.val‖ : ℝ) : ℂ) ^ a = (z a ^ f)⁻¹ := by
    have hb : 0 < ‖π.val‖ := norm_pos_iff.mpr π.ne_zero
    dsimp only [z]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
      ← Complex.ofReal_log hb.le, hπ, Real.log_inv, hN, Nat.cast_pow, Real.log_pow,
      ← Complex.exp_nat_mul, ← Complex.exp_neg]
    push_cast
    congr 1
    ring
  have hpole (a : ℂ) :
      sLocalPoleContributes χ (Sum.inr v) a ↔ U ∧ ψ π = z a ^ f := by
    rw [sLocalPoleContributes_finite_iff_tateFactor, (h a).2.1]
    change (U ∧ ψ π * ((‖π.val‖ : ℝ) : ℂ) ^ a = 1) ↔ _
    rw [hpow, mul_inv_eq_one₀ (pow_ne_zero f (Complex.exp_ne_zero _))]
  by_cases hU : U
  · refine ⟨Polynomial.nthRootsFinset f (ψ π), fun a ↦ ?_⟩
    rw [hpole, Polynomial.mem_nthRootsFinset hf, and_iff_right hU]
    exact eq_comm
  · refine ⟨∅, fun a ↦ ?_⟩
    simp [hpole, hU]

/-- A finite stage whose places lie over one rational prime admits a common norm base,
including the empty stage. -/
private theorem exists_prime_pow_norms_of_same_prime
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ ∀ v : S, ∃ f : ℕ, 0 < f ∧ v.val.asIdeal.absNorm = p ^ f := by
  classical
  by_cases hSne : S.Nonempty
  · let v₀ : S := ⟨hSne.choose, hSne.choose_spec⟩
    let P := v₀.val.asIdeal.under ℤ
    have : NeZero v₀.val.asIdeal := ⟨v₀.val.ne_bot⟩
    refine ⟨P.absNorm, Nat.absNorm_under_prime v₀.val.asIdeal, fun v ↦ ?_⟩
    have hPv : v.val.asIdeal.under ℤ = P := by
      have h := congrArg (fun q : HeightOneSpectrum (𝓞 ℚ) ↦ q.asIdeal.under ℤ) (hsame v v₀)
      simpa [HeightOneSpectrum.under, Ideal.under_under, P] using h
    have : v.val.asIdeal.LiesOver P := ⟨hPv.symm⟩
    exact ⟨_, Ideal.inertiaDeg_pos v.val.asIdeal ℤ, (Ideal.absNorm_pow_inertiaDeg P _).symm⟩
  · exact ⟨2, Nat.prime_two, fun v ↦ (hSne ⟨v.val, v.property⟩).elim⟩

/-- A finite set of possible phases at each finite place determines a global valid
assignment. Each realized phase is assigned to one finite place at every center in its
class. In any closed vertical strip only finitely many poles have no finite contribution. -/
private theorem exists_isValidPoleAssignment_of_phase_finsets (χ : PontryaginDual Jₛ)
    (z : ℂ → ℂ) (Q : S → Finset ℂ)
    (hQ : ∀ (v : S) (a : ℂ), sLocalPoleContributes χ (Sum.inr v) a ↔ z a ∈ Q v) :
    ∃ (E : Finset ℂ) (σ assign : ℂ → Places),
      (∀ u : ℂ, u ∈ E ↔ ∃ (a : ℂ) (v : S),
        z a = u ∧ sLocalPoleContributes χ (Sum.inr v) a) ∧
      (∀ u ∈ E, ∃ v : S, σ u = Sum.inr v ∧
        ∀ a : ℂ, z a = u → sLocalPoleContributes χ (Sum.inr v) a) ∧
      IsValidPoleAssignment χ assign ∧
      (∀ a : ℂ, z a ∈ E → assign a = σ (z a)) ∧
      (∀ A : ℝ, {a : ℂ | a.re ∈ Icc (-A) 1 ∧
        meromorphicOrderAt (fun s ↦ sLocalRhoFactor (chart(χ) s)) a < 0 ∧ z a ∉ E}.Finite) := by
  classical
  let E := (Finset.univ.biUnion Q).filter fun u ↦ ∃ a : ℂ, z a = u
  have hE (u : ℂ) : u ∈ E ↔ ∃ (a : ℂ) (v : S),
      z a = u ∧ sLocalPoleContributes χ (Sum.inr v) a := by
    simp only [E, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨v, hv⟩, a, rfl⟩
      exact ⟨a, v, rfl, (hQ v a).mpr hv⟩
    · rintro ⟨a, v, rfl, hv⟩
      exact ⟨⟨v, (hQ v a).mp hv⟩, a, rfl⟩
  have hplaces {u : ℂ} (hu : u ∈ E) : ∃ v : S, u ∈ Q v := by
    obtain ⟨a, v, rfl, hv⟩ := (hE u).mp hu
    exact ⟨v, (hQ v a).mp hv⟩
  let σ (u : ℂ) : Places := if h : u ∈ E then Sum.inr (hplaces h).choose
    else Sum.inl (Classical.arbitrary (InfinitePlace F))
  have hσ (u : ℂ) (hu : u ∈ E) : ∃ v : S, σ u = Sum.inr v ∧
      ∀ a : ℂ, z a = u → sLocalPoleContributes χ (Sum.inr v) a := by
    refine ⟨(hplaces hu).choose, dite_eq_left hu, fun a ha ↦ (hQ _ a).mpr ?_⟩
    rw [ha]
    exact (hplaces hu).choose_spec
  obtain ⟨fallback, hvalid⟩ := exists_isValidPoleAssignment χ
  let assign (a : ℂ) := if z a ∈ E then σ (z a) else fallback a
  refine ⟨E, σ, assign, hE, hσ, ?_, fun a ha ↦ ite_eq_left ha, fun A ↦ ?_⟩
  · intro a ha
    by_cases he : z a ∈ E
    · obtain ⟨v, hv, hc⟩ := hσ (z a) he
      rw [show assign a = Sum.inr v from (ite_eq_left he).trans hv]
      exact hc a rfl
    · rw [show assign a = fallback a from ite_eq_right he]
      exact hvalid a ha
  · refine (sLocalPoleContributes_archimedean_finite_in_strip χ A).subset ?_
    rintro a ⟨hre, ha, he⟩
    obtain ⟨w | v, hv⟩ := (sLocalPoleContributes_exists_iff χ a).mp ha
    · exact ⟨hre, w, hv⟩
    · exact (he ((hE _).mpr ⟨a, v, rfl, hv⟩)).elim

/-- Paper: Theorem 7.1.2.3, pp. 317–323. If all finite places lie over a single rational
prime, there is a valid assignment constant on each realized finite pole phase. Every strip
contains only finitely many poles outside those classes.
Deviation: A shared pole is assigned once, with every pole in a given phase class assigned
to the same contributing place. -/
theorem exists_isValidPoleAssignment_of_same_prime_phases (χ : PontryaginDual Jₛ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧
      let z (a : ℂ) := Complex.exp ((Real.log (p : ℝ) : ℂ) * a)
      ∃ (Q : S → Finset ℂ) (E : Finset ℂ) (σ assign : ℂ → Places),
        (∀ (v : S) (a : ℂ), sLocalPoleContributes χ (Sum.inr v) a ↔ z a ∈ Q v) ∧
        (∀ u : ℂ, u ∈ E ↔ ∃ (a : ℂ) (v : S),
          z a = u ∧ sLocalPoleContributes χ (Sum.inr v) a) ∧
        (∀ u ∈ E, ∃ v : S, σ u = Sum.inr v ∧
          ∀ a : ℂ, z a = u → sLocalPoleContributes χ (Sum.inr v) a) ∧
        IsValidPoleAssignment χ assign ∧
        (∀ a : ℂ, z a ∈ E → assign a = σ (z a)) ∧
        (∀ A : ℝ, {a : ℂ | a.re ∈ Icc (-A) 1 ∧
          meromorphicOrderAt (fun s ↦ sLocalRhoFactor (chart(χ) s)) a < 0 ∧ z a ∉ E}.Finite) := by
  classical
  obtain ⟨p, hp, hdegs⟩ := exists_prime_pow_norms_of_same_prime hsame
  refine ⟨p, hp, ?_⟩
  let z (a : ℂ) := Complex.exp ((Real.log (p : ℝ) : ℂ) * a)
  have hsets (v : S) : ∃ Q : Finset ℂ, ∀ a : ℂ,
      sLocalPoleContributes χ (Sum.inr v) a ↔ z a ∈ Q := by
    obtain ⟨f, hf, hN⟩ := hdegs v
    exact sLocalPoleContributes_finite_phase_finset χ v hf hN
  choose Q hQ using hsets
  obtain ⟨E, σ, assign, h⟩ := exists_isValidPoleAssignment_of_phase_finsets χ z Q hQ
  exact ⟨Q, E, σ, assign, hQ, h⟩

/-- The order of the actual local zeta integral is bounded below by minus the
number of local places, independently of the test vector and the center. -/
theorem sLocalIdelicZFunction_order_ge_neg_card_places
    (χ : PontryaginDual Jₛ) (f : Tests) (a : ℂ) :
    ((-((S.card + Fintype.card (InfinitePlace F) : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (chart(χ) z)) a := by
  classical
  apply le_trans _ (sLocalIdelicZFunction_poles f χ a)
  refine le_min ?_ ?_
  · exact_mod_cast neg_nonpos.mpr (Int.natCast_nonneg _)
  · by_cases h : meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0
    · rw [sLocalRhoFactor_orderAt_pole χ a h]
      apply WithTop.coe_le_coe.mpr
      apply neg_le_neg
      norm_cast
      rw [Nat.add_comm S.card]
      exact Nat.add_le_add (Finset.card_filter_le _ _ |>.trans_eq Finset.card_univ)
        (Finset.card_filter_le _ _ |>.trans_eq (by simp))
    · exact le_trans (by exact_mod_cast neg_nonpos.mpr (Int.natCast_nonneg _)) (le_of_not_gt h)

/-- The norm dilation is an entire unit in the twist coordinate, including at a pole. -/
private theorem normPower_mul_sLocalIdelicZFunction_order
    (χ : PontryaginDual Jₛ) (f : Tests) (a : ℂ) (r : ℝ) (hr : 0 < r) :
    meromorphicOrderAt (fun z ↦ (r : ℂ) ^ (-z) * sLocalIdelicZFunction f (chart(χ) z)) a =
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (chart(χ) z)) a := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hu : AnalyticAt ℂ (fun z : ℂ ↦ (r : ℂ) ^ (-z)) a :=
    (differentiable_neg.const_cpow (Or.inl hrC)).analyticAt a
  have hzero := hu.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hrC))
  exact (meromorphicOrderAt_mul hu.meromorphicAt ((sLocalIdelicZFunction_meromorphic f χ)
    (mem_univ a)).meromorphicAt).trans ((congrArg (· + _) hzero).trans (zero_add _))

/-- A single jet budget works for all norm dilations, centers and test vectors. -/
private theorem normPower_mul_sLocalIdelicZFunction_order_ge_neg_card_places
    (χ : PontryaginDual Jₛ) (f : Tests) (a : ℂ) (r : ℝ) (hr : 0 < r) :
    ((-((S.card + Fintype.card (InfinitePlace F) : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ (r : ℂ) ^ (-z) * sLocalIdelicZFunction f (chart(χ) z)) a := by
  rw [normPower_mul_sLocalIdelicZFunction_order χ f a r hr]
  exact sLocalIdelicZFunction_order_ge_neg_card_places χ f a

section

open Polynomial

open Classical in
/-- Hermite interpolation of a finite set indicator, with all positive jets through order
`M - 1` zero. The same polynomial works at every point of `E`. -/
private theorem exists_hermiteResiduePolynomial (E A : Finset ℂ) (M : ℕ) :
    ∃ P : ℂ[X], ∀ α ∈ E, (X - C α) ^ M ∣ P - C (if α ∈ A then 1 else 0) := by
  classical
  let F (α : ℂ) : ℂ[X] := (X - C α) ^ M
  let p := ∏ α ∈ E.filter (· ∈ A), F α
  let q := ∏ α ∈ E.filter (· ∉ A), F α
  have hpq : IsCoprime p q := by
    apply IsCoprime.prod_left
    intro α hα
    apply IsCoprime.prod_right
    intro β hβ
    have hne : α ≠ β := fun h ↦ (Finset.mem_filter.mp hβ).2 (h ▸ (Finset.mem_filter.mp hα).2)
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit).pow
  obtain ⟨u, v, huv⟩ := hpq
  refine ⟨v * q, fun α hα ↦ ?_⟩
  by_cases h : α ∈ A
  · have hdiv : F α ∣ p := Finset.dvd_prod_of_mem F (Finset.mem_filter.mpr ⟨hα, h⟩)
    have hid : v * q - 1 = -(u * p) := by linear_combination huv
    simpa only [ite_eq_left h, map_one, hid, dvd_neg] using dvd_mul_of_dvd_right hdiv u
  · have hdiv : F α ∣ q := Finset.dvd_prod_of_mem F (Finset.mem_filter.mpr ⟨hα, h⟩)
    simpa only [ite_eq_right h, map_zero, sub_zero] using dvd_mul_of_dvd_right hdiv v

/-- On a sufficiently small circle the normalized integral of a meromorphic germ is constant. -/
private theorem eventually_circleIntegral_eq_residue {W : ℂ → ℂ} {a : ℂ}
    (hW : MeromorphicAt W a) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), circleIntegral W a r / (2 * (Real.pi : ℂ) * Complex.I) =
      complexResidue W a := by
  obtain ⟨R, hR, h⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hW.eventually_analyticAt
  have key (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) (hsR : s < R) :
      circleIntegral W a s = circleIntegral W a r := by
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrs
      Set.countable_empty
    · intro z hz
      have hzR := Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz.1).trans_lt hsR)
      have hza : z ≠ a := fun he ↦ hz.2 (he ▸ Metric.mem_ball_self hr)
      exact (h ⟨hzR, hza⟩).continuousAt.continuousWithinAt
    · intro z hz
      have hzR := Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.1.1).trans hsR)
      have hza : z ≠ a := fun he ↦ hz.1.2 (he ▸ Metric.mem_closedBall_self hr.le)
      exact (h ⟨hzR, hza⟩).differentiableAt
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), circleIntegral W a r = circleIntegral W a (R / 2) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    rcases le_total (R / 2) r with hr' | hr'
    · exact key _ _ (half_pos hR) hr' hr.2
    · exact (key _ _ hr.1 hr' (half_lt_self hR)).symm
  have hfix : complexResidue W a =
      circleIntegral W a (R / 2) / (2 * (Real.pi : ℂ) * Complex.I) := by
    apply (tendsto_const_nhds.congr' ?_).limUnder_eq
    filter_upwards [hev] with r hr
    rw [hr]
  filter_upwards [hev] with r hr
  rw [hfix, hr]

private theorem eventually_circleIntegrable_of_meromorphicAt {W : ℂ → ℂ} {a : ℂ}
    (hW : MeromorphicAt W a) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), CircleIntegrable W a r := by
  obtain ⟨R, hR, h⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hW.eventually_analyticAt
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  refine ContinuousOn.circleIntegrable hr.1.le
    (fun z hz ↦ (h ⟨?_, ?_⟩).continuousAt.continuousWithinAt)
  · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hz).trans_lt hr.2)
  · rintro rfl
    exact hr.1.ne (by simpa using Metric.mem_sphere.mp hz)

/-- The circle residue is linear on meromorphic germs at an arbitrary center. -/
private theorem complexResidue_const_mul_add {F G : ℂ → ℂ} {a : ℂ} (c : ℂ)
    (hF : MeromorphicAt F a) (hG : MeromorphicAt G a) :
    complexResidue (fun z ↦ c * F z + G z) a = c * complexResidue F a + complexResidue G a := by
  have hcF : MeromorphicAt (fun z ↦ c * F z) a := (MeromorphicAt.const c a).mul hF
  have hsum : MeromorphicAt (fun z ↦ c * F z + G z) a := hcF.add hG
  apply (Filter.eventually_const (f := 𝓝[>] (0 : ℝ))).mp
  filter_upwards [eventually_circleIntegral_eq_residue hsum, eventually_circleIntegral_eq_residue hF,
    eventually_circleIntegral_eq_residue hG, eventually_circleIntegrable_of_meromorphicAt hcF,
    eventually_circleIntegrable_of_meromorphicAt hG] with r hs hf hg hcf hgi
  rw [← hs, ← hf, ← hg, circleIntegral.integral_add hcf hgi, circleIntegral.integral_const_mul]
  ring

private theorem complexResidue_germ_congr {F G : ℂ → ℂ} {a : ℂ}
    (he : F =ᶠ[𝓝[≠] a] G) : complexResidue F a = complexResidue G a := by
  obtain ⟨R, hR, h⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ h ⟨?_, ?_⟩]
  · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hz).trans_lt hr.2)
  · rintro rfl
    exact hr.1.ne (by simpa using Metric.mem_sphere.mp hz)

private theorem complexResidue_zero_of_analytic_germ {W H : ℂ → ℂ} {a : ℂ}
    (hH : AnalyticAt ℂ H a) (he : W =ᶠ[𝓝[≠] a] H) :
    complexResidue W a = 0 := by
  have he' : W =ᶠ[𝓝[≠] a] (fun z ↦ ((z - a) * H z) / (z - a)) := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hza
    exact hz.trans (mul_div_cancel_left₀ _ (sub_ne_zero.mpr (mem_compl_singleton_iff.mp hza))).symm
  rw [complexResidue_germ_congr he', complexResidue_div_sub (g := fun z ↦ (z - a) * H z)
    ((analyticAt_id.sub analyticAt_const).mul hH), sub_self, zero_mul]

/-- A correction divisible by the pole bound changes a weighted residue by its constant factor
only. The analytic map may be ramified or even constant at the center. -/
private theorem complexResidue_polynomial_mul_of_pow_dvd_sub {W φ : ℂ → ℂ} {a c : ℂ} {M : ℕ}
    (P : ℂ[X]) (hφ : AnalyticAt ℂ φ a) (hW : MeromorphicAt W a)
    (hord : ((-(M : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt W a)
    (hdiv : (X - C (φ a)) ^ M ∣ P - C c) :
    complexResidue (fun z ↦ P.eval (φ z) * W z) a = c * complexResidue W a := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hpol (z : ℂ) : P.eval (φ z) - c = (φ z - φ a) ^ M * Q.eval (φ z) := by
    simpa using congrArg (Polynomial.eval (φ z)) hQ
  let B (z : ℂ) := (z - a) ^ M * W z
  have hPow : MeromorphicAt (fun z : ℂ ↦ (z - a) ^ M) a := by fun_prop
  have hB : MeromorphicAt B a := hPow.mul hW
  have hBo : 0 ≤ meromorphicOrderAt B a := by
    change 0 ≤ meromorphicOrderAt ((fun z : ℂ ↦ (z - a) ^ M) * W) a
    have hmono : meromorphicOrderAt (fun z : ℂ ↦ (z - a) ^ M) a = M :=
      meromorphicOrderAt_pow_id_sub_const
    rw [meromorphicOrderAt_mul hPow hW, hmono]
    have h := add_le_add_right hord (M : WithTop ℤ)
    simpa [← WithTop.coe_add] using h
  obtain ⟨H, hH, he⟩ := hB.meromorphicOrderAt_nonneg_iff.mp hBo
  let D (z : ℂ) := (P.eval (φ z) - c) * W z
  have hfactor : D =ᶠ[𝓝[≠] a] (fun z ↦ (dslope φ a z) ^ M * Q.eval (φ z) * H z) := by
    filter_upwards [he] with z hz
    have hs : φ z - φ a = (z - a) * dslope φ a z := (sub_smul_dslope φ a z).symm
    change (P.eval (φ z) - c) * W z = _
    rw [← hz, hpol, hs, mul_pow]
    dsimp [B]
    ring
  have hD : MeromorphicAt D a :=
    (((P.differentiable.analyticAt _).comp hφ).sub analyticAt_const).meromorphicAt.mul hW
  have hzero : complexResidue D a = 0 :=
    complexResidue_zero_of_analytic_germ
      (((hφ.dslope a).pow M).mul ((Q.differentiable.analyticAt _).comp hφ) |>.mul hH) hfactor
  have heq : (fun z ↦ P.eval (φ z) * W z) = (fun z ↦ c * W z + D z) := by
    funext z
    dsimp [D]
    ring
  rw [heq, complexResidue_const_mul_add c hW hD, hzero, add_zero]

/-- A finite polynomial in an analytic multiplier extracts a finite linear combination of
the residues after multiplication by its powers. -/
private theorem complexResidue_polynomial_mul_eq_sum {W φ : ℂ → ℂ} {a : ℂ} (P : ℂ[X])
    (hφ : AnalyticAt ℂ φ a) (hW : MeromorphicAt W a) :
    complexResidue (fun z ↦ P.eval (φ z) * W z) a =
      ∑ j ∈ P.support, P.coeff j * complexResidue (fun z ↦ (φ z) ^ j * W z) a := by
  classical
  let F (j : ℕ) (z : ℂ) := (φ z) ^ j * W z
  have hm (j : ℕ) : MeromorphicAt (F j) a := (hφ.pow j).meromorphicAt.mul hW
  have hsum (s : Finset ℕ) : complexResidue (fun z ↦ ∑ j ∈ s, P.coeff j * F j z) a =
      ∑ j ∈ s, P.coeff j * complexResidue (F j) a := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        complexResidue_zero_of_analytic_germ (a := a) (H := fun _ ↦ 0) analyticAt_const
          Filter.EventuallyEq.rfl
    | @insert j s hjs ih =>
      simp only [Finset.sum_insert hjs]
      rw [complexResidue_const_mul_add (P.coeff j) (hm j) ?_, ih]
      fun_prop (disch := exact hm _)
  rw [show (fun z ↦ P.eval (φ z) * W z) = (fun z ↦ ∑ j ∈ P.support, P.coeff j * F j z) by
    funext z
    rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ ↦ mul_assoc _ _ _)]
  exact hsum P.support

open Classical in
/-- The indicator at a pole equals a finite linear combination of residues of analytic
multipliers. One polynomial works simultaneously at all fibers above the finite phase set. -/
private theorem exists_hermiteResiduePolynomial_eq_sum (E A : Finset ℂ) (M : ℕ) :
    ∃ P : ℂ[X], ∀ {a : ℂ} {φ W : ℂ → ℂ}, φ a ∈ E → AnalyticAt ℂ φ a → MeromorphicAt W a →
      ((-(M : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt W a →
      (if φ a ∈ A then complexResidue W a else 0) =
        ∑ j ∈ P.support, P.coeff j * complexResidue (fun z ↦ (φ z) ^ j * W z) a := by
  classical
  obtain ⟨P, hP⟩ := exists_hermiteResiduePolynomial E A M
  refine ⟨P, fun {a φ W} hE hφ hW hord ↦ ?_⟩
  rw [← complexResidue_polynomial_mul_eq_sum P hφ hW,
    complexResidue_polynomial_mul_of_pow_dvd_sub P hφ hW hord (hP _ hE)]
  split <;> simp

open Classical in
/-- A single polynomial filters the higher-order residues above a finite exponential phase set,
with no restriction on the period parameter. -/
private theorem exists_hermiteResiduePolynomial_exp_sum (E A : Finset ℂ) (M : ℕ) :
    ∃ P : ℂ[X], ∀ {a L : ℂ} {W : ℂ → ℂ}, Complex.exp (L * a) ∈ E → MeromorphicAt W a →
      ((-(M : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt W a →
      (if Complex.exp (L * a) ∈ A then complexResidue W a else 0) =
        ∑ j ∈ P.support, P.coeff j * complexResidue (fun z ↦ Complex.exp (L * z) ^ j * W z) a := by
  obtain ⟨P, hP⟩ := exists_hermiteResiduePolynomial_eq_sum E A M
  refine ⟨P, fun {a L W} hE hW hord ↦ ?_⟩
  exact hP (φ := fun z ↦ Complex.exp (L * z)) hE (by fun_prop) hW hord

end

private theorem inverseNorm_dilation_cpow (p r : ℝ) (hp : 0 < p) (hr : 0 < r)
    (j : ℕ) (s : ℂ) :
    Complex.exp ((Real.log p : ℂ) * s) ^ j * (r : ℂ) ^ (-s) =
      ((p⁻¹ ^ j * r : ℝ) : ℂ) ^ (-s) := by
  have hpr : 0 < p⁻¹ ^ j * r := mul_pos (pow_pos (inv_pos.mpr hp) _) hr
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpr.ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log hpr.le,
    Real.log_mul (pow_ne_zero j (inv_ne_zero hp.ne')) hr.ne', Real.log_pow, Real.log_inv,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem inverseNorm_dilation_character {G : Type*} [CommGroup G] [TopologicalSpace G]
    (χ : PontryaginDual G) (u g : G) (j : ℕ) :
    (χ u : ℂ)^j * star (χ (u ^ j * g) : ℂ) = star (χ g : ℂ) := by
  have hh (y : Circle) : star (y : ℂ) = (y⁻¹ : Circle) := (Circle.coe_inv_eq_conj y).symm
  rw [hh, hh, map_mul, map_pow, ← Circle.coe_pow, ← Circle.coe_mul]
  congr 1
  simp
  rfl

private theorem inverseNorm_dilation_sum {X : Type*} {σ : Type*} [DecidableEq σ]
    (Q D : Finset ℂ) (hD : D ⊆ Q) (assign : ℂ → σ) (v : σ)
    (T : ℂ → X → ℂ) (joints : ℕ → ℂ → X → ℂ) (support : Finset ℕ) (c : ℕ → ℂ)
    (hfilter : ∀ a ∈ Q, a ∉ D → ∀ x,
      (if assign a = v then T a x else 0) = ∑ j ∈ support, c j * joints j a x) (x : X) :
    ∑ a ∈ Q.filter (assign · = v), T a x =
      (∑ j ∈ support, c j * ∑ a ∈ Q, joints j a x) +
        ∑ a ∈ D, ((if assign a = v then T a x else 0) - ∑ j ∈ support, c j * joints j a x) := by
  classical
  rw [Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := support)]
  let diff (a : ℂ) := (if assign a = v then T a x else 0) - ∑ j ∈ support, c j * joints j a x
  have he : ∑ a ∈ D, diff a = ∑ a ∈ Q, diff a := by
    apply Finset.sum_subset hD
    intro a ha hna
    exact sub_eq_zero.mpr (hfilter a ha hna x)
  change _ = _ + ∑ a ∈ D, diff a
  rw [he]
  simp only [diff, Finset.sum_sub_distrib]
  abel

private theorem finiteDilation_tendstoUniformlyOn {X ι : Type*} {l : Filter ι} (K : Set X)
    (s : Finset ℕ) (c : ℕ → ℂ) (U : ℕ → ι → X → ℂ) (L : ℕ → X → ℂ)
    (corr : X → ℂ) (h : ∀ j ∈ s, TendstoUniformlyOn (U j) (L j) l K) :
    TendstoUniformlyOn (fun h x ↦ (∑ j ∈ s, c j * U j h x) + corr x)
      (fun x ↦ (∑ j ∈ s, c j * L j x) + corr x) l K := by
  have hsum : TendstoUniformlyOn (fun h x ↦ ∑ j ∈ s, c j * U j h x)
      (fun x ↦ ∑ j ∈ s, c j * L j x) l K := by
    induction s using Finset.cons_induction_on with
    | empty =>
      simp only [Finset.sum_empty, Metric.tendstoUniformlyOn_iff, dist_self]
      exact fun ε hε ↦ Eventually.of_forall (fun _ _ _ ↦ hε)
    | cons a t hat ih =>
      simp only [Finset.sum_cons]
      have ha := (uniformContinuous_const_smul (c a)).comp_tendstoUniformlyOn
        (h a (Finset.mem_cons_self _ _))
      exact ha.add (ih (fun j hj ↦ h j (Finset.mem_cons_of_mem hj)))
  rw [Metric.tendstoUniformlyOn_iff] at hsum ⊢
  intro ε hε
  filter_upwards [hsum ε hε] with h hh x hx
  simpa only [dist_add_right] using hh x hx

open Classical in
/-- The distinct poles of the S-local correcting factor in the open horizontal window
of the separately indexed expansion. -/
def sLocalStripPoleWindow (χ : PontryaginDual Jₛ) (A : ℝ) (h : ℝ × ℝ) : Finset ℂ :=
  (finite_rectanglePoles (f := fun z ↦ sLocalRhoFactor (chart(χ) z))
    (a := -A - 1) (b := 2) (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
    (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).toFinset

/-- Paper: Theorem 7.1.2.3, pp. 318, 322. The contribution at one center, retaining
the full Mellin residue and the conjugate character. -/
def sLocalMellinPoleTerm (χ : PontryaginDual Jₛ) (f : Tests) (g : Jₛ) (a : ℂ) : ℂ :=
  star (χ g : ℂ) * complexResidue (fun z ↦ ((((normₛ g).val : ℝ) : ℂ) ^ (-z)) *
    sLocalIdelicZFunction f (chart(χ) z)) a

private theorem mem_sLocalStripPoleWindow {χ : PontryaginDual Jₛ} {A : ℝ} {h : ℝ × ℝ} {a : ℂ} :
    a ∈ sLocalStripPoleWindow χ A h ↔ a.re ∈ Ioo (-A) 1 ∧
      a.im ∈ Ioo h.1 h.2 ∧ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 := by
  exact Set.Finite.mem_toFinset _

private theorem exists_inverseNorm_dilation (p : ℕ) (hp : p.Prime) :
    ∃ u : Jₛ, ((normₛ u).val : ℝ) = (p : ℝ)⁻¹ := by
  obtain ⟨t, ht⟩ := sIdeleQuotientNorm_exists_section F S
  let r : ℝ≥0ˣ := Units.mk0 (p : ℝ≥0) (Nat.cast_ne_zero.mpr hp.ne_zero)
  refine ⟨t r⁻¹, ?_⟩
  rw [ht]
  rfl

private theorem inverseNorm_dilation_rate (u : Jₛ) (hu : ((normₛ u).val : ℝ) ≤ 1)
    (g : Jₛ) (hg : ((normₛ g).val : ℝ) < 1) (j : ℕ) : ((normₛ (u ^ j * g)).val : ℝ) < 1 := by
  rw [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, NNReal.coe_mul, NNReal.coe_pow]
  calc
    _ ≤ 1 * ((normₛ g).val : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hu) (by positivity)
    _ < 1 := by simpa using hg

private theorem singlePrime_monomial_residue (χ : PontryaginDual Jₛ) (f : Tests) (p : ℕ)
    (hp : p.Prime) (u : Jₛ) (hu : ((normₛ u).val : ℝ) = (p : ℝ)⁻¹) (g : Jₛ) (a : ℂ) (j : ℕ) :
    star (χ g : ℂ) * complexResidue (fun z ↦
      Complex.exp ((Real.log (p : ℝ) : ℂ) * z) ^ j *
        ((((normₛ g).val : ℝ) : ℂ) ^ (-z) * sLocalIdelicZFunction f (chart(χ) z))) a =
      (χ u : ℂ) ^ j * sLocalMellinPoleTerm χ f (u ^ j * g) a := by
  have hpos : 0 < ((normₛ g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hnorm : ((normₛ (u ^ j * g)).val : ℝ) = (p : ℝ)⁻¹ ^ j * ((normₛ g).val : ℝ) := by
    rw [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, NNReal.coe_mul, NNReal.coe_pow, hu]
  have he (z : ℂ) := inverseNorm_dilation_cpow (p : ℝ) ((normₛ g).val : ℝ)
    (Nat.cast_pos.mpr hp.pos) hpos j z
  simp only [sLocalMellinPoleTerm, ← mul_assoc, hnorm, he, inverseNorm_dilation_character]

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. Over one rational prime a fixed, valid
assignment gives each place's complete residue sum as a finite combination of dilated joint
sums, up to the contribution of finitely many archimedean centers. The coefficients,
dilations and cutoff are independent of the test and the idèle. -/
theorem exists_sLocalSinglePrime_placeSum_dilations (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    ∃ assign : ℂ → Places, IsValidPoleAssignment χ assign ∧
      ∃ u : Jₛ, ((normₛ u).val : ℝ) ≤ 1 ∧
      ∀ v : Places, ∃ (J : Finset ℕ) (c : ℕ → ℂ) (corr : Tests → Jₛ → ℂ),
      ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, ∀ (f : Tests) (g : Jₛ),
        ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v), sLocalMellinPoleTerm χ f g a =
          (∑ j ∈ J, c j * ∑ a ∈ sLocalStripPoleWindow χ A h,
            sLocalMellinPoleTerm χ f (u ^ j * g) a) + corr f g := by
  classical
  obtain ⟨p, hp, _, E, σ, assign, _, _, _, hvalid, hagree, hfin⟩ :=
    exists_isValidPoleAssignment_of_same_prime_phases χ hsame
  let phase (z : ℂ) := Complex.exp ((Real.log (p : ℝ) : ℂ) * z)
  obtain ⟨u, hu⟩ := exists_inverseNorm_dilation (F := F) (S := S) p hp
  have hsmall : ((normₛ u).val : ℝ) ≤ 1 := by
    rw [hu]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  refine ⟨assign, hvalid, u, hsmall, fun v ↦ ?_⟩
  let phases := E.filter (σ · = v)
  let M := S.card + Fintype.card (InfinitePlace F)
  obtain ⟨P, hP⟩ := exists_hermiteResiduePolynomial_exp_sum E phases M
  let c (j : ℕ) := P.coeff j * (χ u : ℂ) ^ j
  have hfinite : {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ∧ phase a ∉ E}.Finite :=
    (hfin A).subset fun _ ha ↦ ⟨Ioo_subset_Icc_self ha.1, ha.2⟩
  let D := hfinite.toFinset
  let corr (f : Tests) (g : Jₛ) := ∑ a ∈ D,
    ((if assign a = v then sLocalMellinPoleTerm χ f g a else 0) -
      ∑ j ∈ P.support, c j * sLocalMellinPoleTerm χ f (u ^ j * g) a)
  refine ⟨P.support, c, corr, ?_⟩
  filter_upwards [eventually_im_mem_Ioo_of_finset D] with h hh f g
  have hD : D ⊆ sLocalStripPoleWindow χ A h := fun a ha ↦ by
    have hm := hfinite.mem_toFinset.mp ha
    exact mem_sLocalStripPoleWindow.mpr ⟨hm.1, hh a ha, hm.2.1⟩
  refine inverseNorm_dilation_sum (X := Jₛ) _ D hD assign v
    (fun a g ↦ sLocalMellinPoleTerm χ f g a)
    (fun j a g ↦ sLocalMellinPoleTerm χ f (u ^ j * g) a) P.support c ?_ g
  intro a ha hna g
  have ha' := mem_sLocalStripPoleWindow.mp ha
  have hE : phase a ∈ E := by
    by_contra hphase
    exact hna (hfinite.mem_toFinset.mpr ⟨ha'.1, ha'.2.2, hphase⟩)
  have hiff : assign a = v ↔ phase a ∈ phases := by
    rw [hagree a hE]
    change σ (phase a) = v ↔ phase a ∈ E.filter (σ · = v)
    simp only [Finset.mem_filter, hE, true_and]
  let r : ℝ := (normₛ g).val
  let W (z : ℂ) := (r : ℂ) ^ (-z) * sLocalIdelicZFunction f (chart(χ) z)
  have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hW : MeromorphicAt W a := by
    have hpow := (differentiable_neg.const_cpow
      (c := (r : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))).analyticAt a
    exact hpow.meromorphicAt.mul ((sLocalIdelicZFunction_meromorphic f χ) (mem_univ a)).meromorphicAt
  have hfilt := hP (a := a) (L := (Real.log (p : ℝ) : ℂ)) (W := W) hE hW
    (normPower_mul_sLocalIdelicZFunction_order_ge_neg_card_places χ f a r hr)
  calc
    _ = star (χ g : ℂ) * (if phase a ∈ phases then complexResidue W a else 0) := by
      by_cases h : assign a = v
      · simp only [ite_eq_left h, ite_eq_left (hiff.mp h)]; rfl
      · simp only [ite_eq_right h, ite_eq_right (fun h' ↦ h (hiff.mpr h')), mul_zero]
    _ = _ := by
      rw [hfilt, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = P.coeff j * (star (χ g : ℂ) * complexResidue
              (fun z ↦ Complex.exp ((Real.log (p : ℝ) : ℂ) * z) ^ j * W z) a) := by ring
        _ = _ := by rw [singlePrime_monomial_residue χ f p hp u hu g a j]; exact (mul_assoc _ _ _).symm

private theorem placeWindow_uniform_of_dilations
    {χ : PontryaginDual Jₛ} {A : ℝ} {assign : ℂ → Places} {v : Places} {u : Jₛ}
    {J : Finset ℕ} {c : ℕ → ℂ} {corr : Tests → Jₛ → ℂ}
    (hid : ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, ∀ (f : Tests) (g : Jₛ),
      ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v), sLocalMellinPoleTerm χ f g a =
        (∑ j ∈ J, c j * ∑ a ∈ sLocalStripPoleWindow χ A h,
          sLocalMellinPoleTerm χ f (u ^ j * g) a) + corr f g)
    {ι X : Type*} {l : Filter ι} {H : ι → ℝ × ℝ} (hH : Tendsto H l (atBot ×ˢ atTop))
    (K : Set X) (f : X → Tests) (g : X → Jₛ) (L : ℕ → X → ℂ)
    (hjoint : ∀ j ∈ J, TendstoUniformlyOn
      (fun i x ↦ ∑ a ∈ sLocalStripPoleWindow χ A (H i), sLocalMellinPoleTerm χ (f x) (u ^ j * g x) a)
      (L j) l K) :
    TendstoUniformlyOn (fun i x ↦ ∑ a ∈ (sLocalStripPoleWindow χ A (H i)).filter (assign · = v),
      sLocalMellinPoleTerm χ (f x) (g x) a)
      (fun x ↦ (∑ j ∈ J, c j * L j x) + corr (f x) (g x)) l K := by
  have he := hH.eventually hid
  apply (finiteDilation_tendstoUniformlyOn K J c _ L (fun x ↦ corr (f x) (g x)) hjoint).congr
  exact he.mono (fun _ hi x _ ↦ (hi (f x) (g x)).symm)

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. A single valid assignment over one rational
prime transfers joint convergence to separate convergence along the same height cutoff.
Each mode transfers on its own: pointwise, uniform on compact sets of idèles, or uniform on
bounded sets of tests at fixed norm less than one. The separate pointwise limits sum to
the joint limit. This result concerns ordered residue sums and does not assert the absolute
summability invoked on p. 389. -/
theorem sLocalSinglePrime_placeLimits_of_joint (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    ∃ assign : ℂ → Places, IsValidPoleAssignment χ assign ∧
    ∀ (L : Tests → Jₛ → ℂ), ∃ limits : Places → Tests → Jₛ → ℂ,
    ∀ {ι : Type*} (l : Filter ι) [l.NeBot] (H : ι → ℝ × ℝ), Tendsto H l (atBot ×ˢ atTop) →
      let joint (i : ι) (f : Tests) (g : Jₛ) := ∑ a ∈ sLocalStripPoleWindow χ A (H i),
        sLocalMellinPoleTerm χ f g a
      let place (v : Places) (i : ι) (f : Tests) (g : Jₛ) :=
        ∑ a ∈ (sLocalStripPoleWindow χ A (H i)).filter (assign · = v), sLocalMellinPoleTerm χ f g a
      ((∀ f g, Tendsto (fun i ↦ joint i f g) l (𝓝 (L f g))) →
        (∀ v f g, Tendsto (fun i ↦ place v i f g) l (𝓝 (limits v f g))) ∧
        ∀ f g, ∑ v, limits v f g = L f g) ∧
      ((∀ f K, IsCompact K → TendstoUniformlyOn (fun i g ↦ joint i f g) (L f) l K) →
        ∀ v f K, IsCompact K → TendstoUniformlyOn (fun i g ↦ place v i f g) (limits v f) l K) ∧
      ((∀ g, ((normₛ g).val : ℝ) < 1 → ∀ B : Set Tests, Bornology.IsVonNBounded ℂ B →
        TendstoUniformlyOn (fun i f ↦ joint i f g) (fun f ↦ L f g) l B) →
        ∀ v g, ((normₛ g).val : ℝ) < 1 → ∀ B : Set Tests, Bornology.IsVonNBounded ℂ B →
        TendstoUniformlyOn (fun i f ↦ place v i f g) (fun f ↦ limits v f g) l B) := by
  classical
  obtain ⟨assign, hvalid, u, hu, h⟩ := exists_sLocalSinglePrime_placeSum_dilations χ A hsame
  choose J c corr hsum using h
  refine ⟨assign, hvalid, fun L ↦ ⟨fun v f g ↦
    (∑ j ∈ J v, c v j * L f (u ^ j * g)) + corr v f g, ?_⟩⟩
  intro ι l _ H hH joint place
  refine ⟨?_, ?_, ?_⟩
  · intro hpoint
    have hv (v : Places) (f : Tests) (g : Jₛ) : Tendsto (fun i ↦ place v i f g) l
        (𝓝 ((∑ j ∈ J v, c v j * L f (u ^ j * g)) + corr v f g)) := by
      have hcomb := (tendsto_finsetSum (J v) (fun j _ ↦
        (hpoint f (u ^ j * g)).const_mul (c v j))).add_const (corr v f g)
      exact hcomb.congr' ((hH.eventually (hsum v)).mono (fun i hi ↦ (hi f g).symm))
    refine ⟨hv, fun f g ↦ ?_⟩
    have ht := tendsto_finsetSum Finset.univ (fun v _ ↦ hv v f g)
    exact tendsto_nhds_unique (ht.congr (fun i ↦ Finset.sum_fiberwise
      (sLocalStripPoleWindow χ A (H i)) assign (sLocalMellinPoleTerm χ f g))) (hpoint f g)
  · intro hcompact v f K hK
    apply placeWindow_uniform_of_dilations (hsum v) hH K (fun _ ↦ f) id _
    intro j _
    let d (g : Jₛ) := u ^ j * g
    exact ((hcompact f (d '' K) (hK.image (continuous_const.mul continuous_id))).comp d).mono
      (fun x hx ↦ mem_image_of_mem d hx)
  · intro hbounded v g hg B hB
    apply placeWindow_uniform_of_dilations (hsum v) hH B id (fun _ ↦ g) _
    intro j _
    exact hbounded (u ^ j * g) (inverseNorm_dilation_rate u hu g hg j) B hB

end

/-! ## Absolute convergence of the place sums -/

section

open scoped Classical

local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "P(" η "," z ")" => ∏ v : S, (finiteHeckeEulerFactor η v.val z)⁻¹
local notation "Z(" f "," χ "," z ")" => sLocalIdelicZFunction f (chart(χ) z)
local notation "strip(" χ "," A ")" => {a : ℂ // a.re ∈ Ioo (-A) 1 ∧
  meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0}
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) normₛ (isProperMap_sIdeleQuotientNorm F S).continuous

/-- Distinct separated heights have distinct floor indices after division by the separation. -/
private theorem injective_floor_scaled_of_separated {ι : Type*} (y : ι → ℝ) {d : ℝ}
    (hd : 0 < d) (hsep : ∀ i j, i ≠ j → d ≤ |y i - y j|) :
    Injective (fun i ↦ ⌊y i / d⌋) := by
  intro i j hij
  by_contra hne
  have hfi := Int.floor_le (y i / d)
  have hfj := Int.floor_le (y j / d)
  have hci := Int.lt_floor_add_one (y i / d)
  have hcj := Int.lt_floor_add_one (y j / d)
  change ⌊y i / d⌋ = ⌊y j / d⌋ at hij
  rw [hij] at hfi hci
  have h : |y i / d - y j / d| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [← sub_div, abs_div, abs_of_pos hd, div_lt_one hd] at h
  exact (hsep i j hne).not_gt h

/-- The inverse-square height weight is summable over every uniformly separated family of
real heights. -/
private theorem summable_inv_sq_of_separated_heights {ι : Type*} (y : ι → ℝ) {d : ℝ}
    (hd : 0 < d) (hsep : ∀ i j, i ≠ j → d ≤ |y i - y j|) :
    Summable (fun i ↦ 1 / (1 + |y i|) ^ 2) := by
  have hnat : Summable (fun n : ℕ ↦ 1 / (1 + (n : ℝ)) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by decide)).comp_injective
      Nat.succ_injective
    exact h.congr (fun n ↦ by simp [add_comm])
  have hint : Summable (fun n : ℤ ↦ 1 / (1 + |(n : ℝ)|) ^ 2) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor <;> exact hnat.congr (fun n ↦ by simp)
  let k (i : ι) := ⌊y i / d⌋
  let B := 2 + d⁻¹
  have hB (i : ι) : 1 + |(k i : ℝ)| ≤ B * (1 + |y i|) := by
    have hci := Int.lt_floor_add_one (y i / d)
    have hfi := Int.floor_le (y i / d)
    have hneg := neg_abs_le (y i / d)
    have hpos := le_abs_self (y i / d)
    rw [abs_div, abs_of_pos hd] at hneg hpos
    have hk : |(k i : ℝ)| ≤ |y i| / d + 1 := by
      rw [abs_le]
      dsimp [k]
      constructor <;> linarith
    rw [div_eq_mul_inv] at hk
    dsimp [B]
    nlinarith [abs_nonneg (y i), inv_pos.mpr hd]
  have hk := hint.comp_injective (injective_floor_scaled_of_separated y hd hsep)
  apply Summable.of_nonneg_of_le (fun i ↦ by positivity) _ (hk.mul_left (B ^ 2))
  intro i
  change 1 / (1 + |y i|) ^ 2 ≤ B ^ 2 * (1 / (1 + |(k i : ℝ)|) ^ 2)
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) (hB i) 2

/-- A separated set of complex points with only finitely many points off the imaginary axis
has a summable inverse-square height weight. -/
private theorem summable_inv_sq_of_separated_axis {P : Set ℂ} {d : ℝ} (hd : 0 < d)
    (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → d ≤ ‖a - b‖)
    (hoff : {a ∈ P | a.re ≠ 0}.Finite) :
    Summable (fun a : P ↦ 1 / (1 + |a.val.im|) ^ 2) := by
  classical
  let S : Set P := {a | a.val.re = 0}
  apply (summable_subtype_and_compl (s := S)).mp
  constructor
  · refine summable_inv_sq_of_separated_heights (fun a : S ↦ a.val.val.im) hd ?_
    intro a b hab
    have hne : a.val.val ≠ b.val.val := fun h ↦ hab (Subtype.ext (Subtype.ext h))
    have h := hsep _ a.val.property _ b.val.property hne
    have ha : a.val.val.re = 0 := a.property
    have hb : b.val.val.re = 0 := b.property
    have he : (a.val.val - b.val.val) = ((a.val.val.im - b.val.val.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [ha, hb]
    rwa [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  · have hs : Sᶜ.Finite := (hoff.preimage Subtype.val_injective.injOn).subset
      (fun a ha ↦ ⟨a.prop, ha⟩)
    let _ := hs.fintype
    exact (hasSum_fintype _).summable

/-- Cauchy's estimate for the residue on a fixed isolating circle, valid at a pole of any
multiplicity and with no regularity assumption at its center. -/
theorem norm_complexResidue_le_circle {W : ℂ → ℂ} {a : ℂ} {r C : ℝ} (hr : 0 < r)
    (hW : ∀ z ∈ Metric.closedBall a r, z ≠ a → AnalyticAt ℂ W z)
    (hcircle : ∀ z ∈ Metric.sphere a r, ‖W z‖ ≤ C) : ‖complexResidue W a‖ ≤ r * C := by
  have hfix : complexResidue W a = circleIntegral W a r / (2 * (Real.pi : ℂ) * Complex.I) := by
    refine (tendsto_const_nhds.congr' ?_).limUnder_eq
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    congr 1
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hs.1 hs.2.le
      Set.countable_empty
    · intro z hz
      have hza : z ≠ a := fun he ↦ hz.2 (he ▸ Metric.mem_ball_self hs.1)
      exact (hW z hz.1 hza).continuousAt.continuousWithinAt
    · intro z hz
      have hza : z ≠ a := fun he ↦ hz.1.2 (he ▸ Metric.mem_closedBall_self hs.1.le)
      exact (hW z (Metric.ball_subset_closedBall hz.1.1) hza).differentiableAt
  rw [hfix, div_eq_inv_mul]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hcircle

/-- In the one-prime case the inverse-square height weight is summable over the actual
open-strip pole set used in the separate-place rectangle sums. -/
theorem summable_sLocalStripPoles_inv_height_sq (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    Summable (fun a : strip(χ, A) ↦ 1 / (1 + |a.val.im|) ^ 2) := by
  obtain ⟨d, hd, hsep⟩ := sLocalStripPoles_uniformly_discrete_of_same_prime χ A hsame
  apply summable_inv_sq_of_separated_axis (P := {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
    meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0}) hd
  · rintro a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ hab
    exact hsep a ⟨⟨ha.1.le, ha.2.le⟩, ha'⟩ b ⟨⟨hb.1.le, hb.2.le⟩, hb'⟩ hab
  · apply (sLocalPoleContributes_archimedean_finite_in_strip χ A).subset
    rintro a ⟨⟨ha, hpole⟩, haoff⟩
    refine ⟨⟨ha.1.le, ha.2.le⟩, ?_⟩
    obtain ⟨w | v, hv⟩ := (sLocalPoleContributes_exists_iff χ a).mp hpole
    · exact ⟨w, hv⟩
    · obtain ⟨m, t, _, _, he⟩ := hv
      exact (haoff (by rw [he, Complex.mul_I_re, Complex.ofReal_im, neg_zero])).elim

/-- The inverse-square height weight is summable over the actual distinct strip poles,
for every finite set of places. Poles assigned to a given finite place have separated
ordinates, and only finitely many archimedean poles lie in the strip. -/
theorem summable_sLocalStripPoles_inv_height_sq_all (χ : PontryaginDual Jₛ) (A : ℝ) :
    Summable (fun a : strip(χ, A) ↦ 1 / (1 + |a.val.im|) ^ 2) := by
  classical
  obtain ⟨assign, hassign⟩ := exists_isValidPoleAssignment χ
  let fiber (v : Places) : Set (strip(χ, A)) := {a | assign a.val = v}
  have hpart (a : strip(χ, A)) : ∃! v, a ∈ fiber v :=
    ⟨assign a.val, rfl, fun _ h ↦ h.symm⟩
  have hcontrib {v : Places} (a : fiber v) : sLocalPoleContributes χ v a.val.val := by
    have h := hassign a.val.val a.val.prop.2
    have ha : assign a.val.val = v := a.prop
    rwa [ha] at h
  apply (summable_partition (s := fiber) (fun a ↦ by positivity) hpart).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro v
  cases v with
  | inl w =>
    have hfin := sLocalPoleContributes_archimedean_finite_in_strip χ A
    have hf : (fiber (.inl w)).Finite := (hfin.preimage
      (f := fun a : strip(χ, A) ↦ a.val) Subtype.val_injective.injOn).subset fun a ha ↦
        ⟨⟨a.prop.1.1.le, a.prop.1.2.le⟩, w, hcontrib ⟨a, ha⟩⟩
    let _ := hf.fintype
    exact (hasSum_fintype _).summable
  | inr v =>
    let T := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
    have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    have hT : 0 < T := div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos hq)
    apply summable_inv_sq_of_separated_heights (fun a : fiber (.inr v) ↦ a.val.val.im) hT
    intro a b hab
    obtain ⟨k, hk⟩ := sLocalPoleContributes_finite_sub χ v (hcontrib b) (hcontrib a)
    have hk₀ : k ≠ 0 := by
      intro h
      have h₀ : a.val.val = b.val.val := sub_eq_zero.mp (by simpa [h] using hk)
      exact hab (Subtype.ext (Subtype.ext h₀))
    have hki : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk₀
    have him : a.val.val.im - b.val.val.im = (k : ℝ) * T := by
      simpa only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re] using congrArg Complex.im hk
    rw [him, abs_mul, abs_of_pos hT]
    exact le_mul_of_one_le_left hT.le hki

/-- Every bounded height range contains only finitely many actual open-strip poles. -/
private theorem eventually_sLocalStripPoles_abs_im_gt (χ : PontryaginDual Jₛ) (A T : ℝ) :
    ∀ᶠ a : strip(χ, A) in cofinite, T < |a.val.im| := by
  rw [eventually_cofinite]
  have hf := finite_rectanglePoles (f := fun z ↦ sLocalRhoFactor (chart(χ) z))
    (a := -A - 1) (b := 2) (σ₁ := -A) (σ₂ := 1) (t₁ := -T - 1) (t₂ := T + 1)
    (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)
  refine (hf.preimage (f := fun a : strip(χ, A) ↦ a.val) Subtype.val_injective.injOn).subset ?_
  intro a ha
  have hl := abs_le.mp (not_lt.mp ha)
  exact ⟨a.property.1, ⟨by linarith [hl.1], by linarith [hl.2]⟩, a.property.2⟩

open Classical in
/-- A summable bound on all but finitely many strip poles yields uniform convergence of each
assigned rectangle sum. The exceptional terms can be arbitrary functions of the parameter. -/
private theorem tendstoUniformlyOn_separatePlacePartialSum_of_cofinite_bound {ι X Y : Type*}
    [NormedAddCommGroup Y] [CompleteSpace Y] {f : ℂ → ℂ} {a b σ₁ σ₂ : ℝ} (hf : MeromorphicOn f (Complex.re ⁻¹' Ioo a b))
    (hσ₁ : a < σ₁) (hσ₂ : σ₂ < b) (assign : ℂ → ι) (term : ℂ → X → Y) (K : Set X)
    (M : {z : ℂ // z.re ∈ Ioo σ₁ σ₂ ∧ meromorphicOrderAt f z < 0} → ℝ) (hM : Summable M)
    (hbound : ∀ᶠ z in cofinite, ∀ x ∈ K, ‖term z.val x‖ ≤ M z) (v : ι) :
    let P := {z : ℂ // z.re ∈ Ioo σ₁ σ₂ ∧ meromorphicOrderAt f z < 0}
    let rect (h : ℝ × ℝ) := (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hf hσ₁ hσ₂).toFinset
    TendstoUniformlyOn (fun h x ↦ ∑ z ∈ (rect h).filter (assign · = v), term z x)
      (fun x ↦ ∑' z : P, if assign z.val = v then term z.val x else 0) (atBot ×ˢ atTop) K := by
  classical
  intro P rect
  let lift (h : ℝ × ℝ) : ↥(rect h) ↪ P := ⟨fun z ↦ ⟨z.val, by
    have hz := (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hf hσ₁ hσ₂).mem_toFinset.mp z.prop
    exact ⟨hz.1, hz.2.2⟩⟩, fun _ _ he ↦ Subtype.ext (congrArg (fun z : P ↦ z.val) he)⟩
  let t (h : ℝ × ℝ) : Finset P := (rect h).attach.map (lift h)
  have ht : Tendsto t (atBot ×ˢ atTop) atTop := by
    refine tendsto_atTop.mpr fun E ↦ ?_
    have hwin (z : P) : ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, z.val.im ∈ Ioo h.1 h.2 :=
      (eventually_lt_atBot z.val.im).prod_mk (eventually_gt_atTop z.val.im)
    filter_upwards [(eventually_all_finset E).mpr (fun z _ ↦ hwin z)] with h hh z hz
    have hrect : z.val ∈ rect h :=
      (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hf hσ₁ hσ₂).mem_toFinset.mpr
        ⟨z.property.1, hh z hz, z.property.2⟩
    exact Finset.mem_map.mpr ⟨⟨z.val, hrect⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  let G (z : P) (x : X) := if assign z.val = v then term z.val x else 0
  have hg : ∀ᶠ z in cofinite, ∀ x ∈ K, ‖G z x‖ ≤ M z := by
    filter_upwards [hbound] with z hz x hx
    by_cases he : assign z.val = v
    · simpa [G, he] using hz x hx
    · simpa [G, he] using (norm_nonneg _).trans (hz x hx)
  have hpart (h : ℝ × ℝ) (x : X) :
      (∑ z ∈ (rect h).filter (assign · = v), term z x) = ∑ z ∈ t h, G z x := by
    dsimp only [t, G]
    rw [Finset.sum_map]
    change _ = ∑ z ∈ (rect h).attach, if assign z.val = v then term z.val x else 0
    rw [Finset.sum_attach (rect h) (fun z ↦ if assign z = v then term z x else 0),
      ← Finset.sum_filter]
  intro V hU
  filter_upwards [ht.eventually (tendstoUniformlyOn_tsum_of_cofinite_eventually hM hg V hU)]
    with h hh x hx
  rw [hpart]
  exact hh x hx

/-- For finitely many translates of one nonzero entire function, every sufficiently
small circle radius admits a positive lower bound common to all the translates. -/
private theorem finite_translates_lower_bound_on_small_circles (D : Finset ℂ) (Q : ℂ → ℂ)
    (hQ : Differentiable ℂ Q) (hq : ∃ w : ℂ, Q w ≠ 0) :
    ∃ r > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < r → ∃ ε > (0 : ℝ),
      ∀ a ∈ D, ∀ u : ℂ, ‖u‖ = δ → ε ≤ ‖Q (a + u)‖ := by
  classical
  obtain ⟨w, hw⟩ := hq
  have hlocal (a : ℂ) : ∀ᶠ u in 𝓝[≠] (0 : ℂ), Q (a + u) ≠ 0 := by
    have hdiff : Differentiable ℂ (fun u : ℂ ↦ Q (a + u)) :=
      hQ.comp ((differentiable_const a).add differentiable_id)
    have ha : AnalyticOnNhd ℂ (fun u : ℂ ↦ Q (a + u)) univ :=
      fun u _ ↦ hdiff.analyticAt u
    refine ((ha 0 trivial).eventually_eq_zero_or_eventually_ne_zero).resolve_left ?_
    intro hz
    have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ (0 : ℂ)) hz
    exact hw (by simpa using hall (mem_univ (w - a)))
  have hall : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ∀ a ∈ D, Q (a + u) ≠ 0 :=
    (Filter.eventually_all_finset D).mpr fun a _ ↦ hlocal a
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hall
  refine ⟨r, hr, fun δ hδ hδr ↦ ?_⟩
  let K : Set (ℂ × ℂ) := (D : Set ℂ) ×ˢ Metric.sphere 0 δ
  have hK : IsCompact K := D.finite_toSet.isCompact.prod (isCompact_sphere _ _)
  have hbound (q : ℂ × ℂ) (hqK : q ∈ K) : Q (q.1 + q.2) ≠ 0 := by
    have hnorm := mem_sphere_zero_iff_norm.mp hqK.2
    apply hball (a := q.2) _ q.1 hqK.1
    refine ⟨Metric.mem_ball.mpr (by simpa [hnorm] using hδr), ?_⟩
    rintro hzero
    have he : q.2 = 0 := hzero
    exact hδ.ne' (hnorm.symm.trans (by simp [he]))
  by_cases hn : K.Nonempty
  · obtain ⟨q, hqK, hmin⟩ := hK.exists_isMinOn hn
      ((hQ.continuous.comp (continuous_fst.add continuous_snd)).norm.continuousOn)
    refine ⟨‖Q (q.1 + q.2)‖, norm_pos_iff.mpr (hbound q hqK), fun a ha u hu ↦ ?_⟩
    exact hmin (show (a, u) ∈ K from ⟨ha, mem_sphere_zero_iff_norm.mpr hu⟩)
  · exact ⟨1, zero_lt_one, fun a ha u hu ↦
      (hn ⟨(a, u), ha, mem_sphere_zero_iff_norm.mpr hu⟩).elim⟩

/-- The reciprocal finite Euler product is entire and is nonzero at exponent one. -/
private theorem reciprocal_euler_product_entire_nonzero (η : U) :
    Differentiable ℂ (fun s : ℂ ↦ P(η,s)) ∧ P(η,1) ≠ 0 := by
  classical
  constructor
  · apply Differentiable.fun_finsetProd
    intro v _
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp only [inv_inv]
      have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        ((Ideal.absNorm_eq_zero_iff).not.mpr v.val.ne_bot)
      exact (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_neg.const_cpow (Or.inl hq)))
    · exact differentiable_const _
  · apply Finset.prod_ne_zero_iff.mpr
    intro v _
    unfold finiteHeckeEulerFactor
    split_ifs
    · rw [inv_inv]
      have hq : (1 : ℝ) < v.val.asIdeal.absNorm := by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val
      have hlt : ‖(ideleClassNormTwist η 0).localValue v.val *
          (v.val.asIdeal.absNorm : ℂ) ^ (-(1 : ℂ))‖ < 1 := by
        rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
          ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq)]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
      exact fun he ↦ hlt.ne (by rw [← sub_eq_zero.mp he, norm_one])
    · simp

/-- At places of norm a power of a common base, equality of two phases identifies the
whole corresponding translates of the pole-clearing product. -/
private theorem reciprocal_euler_product_add_eq_of_phase_eq (η : U) (p : ℕ)
    (hdegs : ∀ v : S, ∃ f : ℕ, 0 < f ∧ v.val.asIdeal.absNorm = p ^ f)
    {a b : ℂ} (hab : Complex.exp ((Real.log (p : ℝ) : ℂ) * a) =
      Complex.exp ((Real.log (p : ℝ) : ℂ) * b)) (u : ℂ) :
    P(η,a + u) = P(η,b + u) := by
  classical
  have hphase : Complex.exp ((Real.log (p : ℝ) : ℂ) * (a + u)) =
      Complex.exp ((Real.log (p : ℝ) : ℂ) * (b + u)) := by
    simp only [mul_add, Complex.exp_add, hab]
  apply Finset.prod_congr rfl
  intro v _
  obtain ⟨f, _, hf⟩ := hdegs v
  have hq : 0 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt (HeightOneSpectrum.one_lt_absNorm v.val)
  have hpow (x : ℂ) : (v.val.asIdeal.absNorm : ℂ) ^ (-x) =
      (Complex.exp ((Real.log (p : ℝ) : ℂ) * x) ^ f)⁻¹ := by
    rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
      ← Complex.ofReal_log hq.le, hf, Nat.cast_pow, Real.log_pow,
      ← Complex.exp_nat_mul, ← Complex.exp_neg]
    push_cast
    congr 1
    ring
  simp only [finiteHeckeEulerFactor, hpow, hphase]

/-- A finite set of exponential phases admits a uniform positive lower bound for the
reciprocal Euler product on circles about all centers with those phases. Every sufficiently
small positive radius is admissible, with a bound depending on the chosen radius. -/
private theorem reciprocal_euler_product_lower_bound_on_phase_circles (η : U) (p : ℕ)
    (hdegs : ∀ v : S, ∃ f : ℕ, 0 < f ∧ v.val.asIdeal.absNorm = p ^ f) (E : Finset ℂ) :
    ∃ r > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < r → ∃ ε > (0 : ℝ), ∀ a : ℂ,
      Complex.exp ((Real.log (p : ℝ) : ℂ) * a) ∈ E →
      ∀ u : ℂ, ‖u‖ = δ → ε ≤ ‖P(η,a + u)‖ := by
  classical
  let phase (a : ℂ) := Complex.exp ((Real.log (p : ℝ) : ℂ) * a)
  let D := E.image (Function.invFun phase)
  obtain ⟨hd, h₁⟩ := reciprocal_euler_product_entire_nonzero (S := S) η
  obtain ⟨r, hr, h⟩ := finite_translates_lower_bound_on_small_circles D
    (fun s : ℂ ↦ P(η,s)) hd ⟨1, h₁⟩
  refine ⟨r, hr, fun δ hδ hδr ↦ ?_⟩
  obtain ⟨ε, hε, hb⟩ := h δ hδ hδr
  refine ⟨ε, hε, fun a ha u hu ↦ ?_⟩
  have he : phase a = phase (Function.invFun phase (phase a)) :=
    Function.apply_invFun_apply.symm
  rw [reciprocal_euler_product_add_eq_of_phase_eq η p hdegs he u]
  exact hb _ (Finset.mem_image_of_mem _ ha) u hu

/-- Paper: Theorem 7.1.2.3, pp. 317–323. If all finite places in the stage lie over
one rational prime, every sufficiently small fixed circle radius gives a uniform positive
lower bound on the product of reciprocal finite Euler factors around all genuine finite
pole centers. This applies to any global unitary lift of the stage character.
Deviation: The lower bound concerns the actual shifted finite Euler denominators. -/
theorem reciprocal_finite_euler_product_lower_bound_on_single_prime_circles
    (χ : PontryaginDual (SIdeleQuotient F S)) (η : U)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    ∃ r > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < r → ∃ ε > (0 : ℝ), ∀ a : ℂ,
      (∃ v : S, sLocalPoleContributes χ (Sum.inr v) a) →
      ∀ u : ℂ, ‖u‖ = δ → ε ≤ ‖P(η,a + u)‖ := by
  classical
  obtain ⟨p, _, hd⟩ := exists_prime_pow_norms_of_same_prime hsame
  let phase (a : ℂ) := Complex.exp ((Real.log (p : ℝ) : ℂ) * a)
  have hsets (v : S) : ∃ E : Finset ℂ, ∀ a : ℂ,
      sLocalPoleContributes χ (Sum.inr v) a ↔ phase a ∈ E := by
    obtain ⟨f, hf, hn⟩ := hd v
    exact sLocalPoleContributes_finite_phase_finset χ v hf hn
  choose E hE using hsets
  obtain ⟨r, hr, h⟩ := reciprocal_euler_product_lower_bound_on_phase_circles η p hd
    (Finset.univ.biUnion E)
  refine ⟨r, hr, fun δ hδ hδr ↦ ?_⟩
  obtain ⟨ε, hε, hb⟩ := h δ hδ hδr
  refine ⟨ε, hε, fun a ha ↦ ?_⟩
  obtain ⟨v, hv⟩ := ha
  exact hb a (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, (hE v a).mp hv⟩)

/-- Every sufficiently high strip pole is contributed by a finite place. -/
private theorem sLocalStripPoles_high_finite_place (χ : PontryaginDual Jₛ) (A : ℝ) :
    ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| →
      ∃ v : S, sLocalPoleContributes χ (Sum.inr v) a.val := by
  let B := {a : ℂ | a.re ∈ Icc (-A) 1 ∧ ∃ w : InfinitePlace F,
    sLocalPoleContributes χ (Sum.inl w) a}
  have hB : B.Finite := sLocalPoleContributes_archimedean_finite_in_strip χ A
  obtain ⟨T, hT⟩ := hB.isCompact.bddAbove_image Complex.continuous_im.abs.continuousOn
  refine ⟨T, fun a ha ↦ ?_⟩
  obtain ⟨w | v, hv⟩ := (sLocalPoleContributes_exists_iff χ a.val).mp a.prop.2
  · have he : a.val ∈ B := ⟨⟨a.prop.1.1.le, a.prop.1.2.le⟩, w, hv⟩
    exact (ha.not_ge (hT ⟨a.val, he, rfl⟩)).elim
  · exact ⟨v, hv⟩

/-- One radius isolates all finite centers, and the product clearing the finite poles
is bounded below on every circle of that radius. -/
private theorem sLocalFinitePoles_isolating_circles (χ : PontryaginDual Jₛ) (η : U)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    ∃ r ∈ Ioo (0 : ℝ) 1, ∃ ε > (0 : ℝ), ∀ a : ℂ,
      (∃ v : S, sLocalPoleContributes χ (Sum.inr v) a) →
      a.re = 0 ∧
      (∀ z ∈ Metric.closedBall a r, z ≠ a →
        0 ≤ meromorphicOrderAt (fun s ↦ sLocalRhoFactor (chart(χ) s)) z) ∧
      ∀ z ∈ Metric.sphere a r, ε ≤ ‖P(η,z)‖ := by
  obtain ⟨d, hd, hsep⟩ := sLocalStripPoles_uniformly_discrete_of_same_prime χ 1 hsame
  obtain ⟨R, hR, hcircle⟩ :=
    reciprocal_finite_euler_product_lower_bound_on_single_prime_circles χ η hsame
  let r := min 1 (min d R) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hlt : r < min 1 (min d R) := half_lt_self (lt_min zero_lt_one (lt_min hd hR))
  have hr1 : r < 1 := hlt.trans_le (min_le_left _ _)
  have hrd : r < d := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrR : r < R := hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ε, hε, heuler⟩ := hcircle r hr hrR
  refine ⟨r, ⟨hr, hr1⟩, ε, hε, fun a ha ↦ ?_⟩
  obtain ⟨v, hv⟩ := ha
  have har : a.re = 0 := by
    obtain ⟨m, t, _, _, he⟩ := hv
    rw [he, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  have hap := (sLocalPoleContributes_exists_iff χ a).mpr ⟨Sum.inr v, hv⟩
  refine ⟨har, fun z hz hne ↦ ?_, fun z hz ↦ ?_⟩
  · have hdist : ‖z - a‖ ≤ r := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hz
    have hre : |z.re| ≤ r := by simpa [Complex.sub_re, har] using (Complex.abs_re_le_norm (z-a)).trans hdist
    apply le_of_not_gt
    intro hpole
    have hza := hsep z ⟨⟨by linarith [(abs_le.mp hre).1], by linarith [(abs_le.mp hre).2]⟩, hpole⟩
      a ⟨by simp [har], hap⟩ hne
    exact hrd.not_ge (hza.trans hdist)
  · have hdist : ‖z - a‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    simpa only [add_sub_cancel] using heuler a ⟨v, hv⟩ (z-a) hdist

/-- On a compact set of ideles the Mellin kernel is bounded throughout the vertical
strip containing the isolating circles of finite poles. -/
private theorem sLocalNormPower_bounded_on_compact_strip (K : Set Jₛ) (hK : IsCompact K)
    (lo hi : ℝ) :
    ∃ D ≥ (0 : ℝ), ∀ g ∈ K, ∀ z : ℂ, z.re ∈ Icc lo hi →
      ‖(((normₛ g).val : ℝ) : ℂ) ^ (-z)‖ ≤ D := by
  let n (g : Jₛ) : ℝ := (normₛ g).val
  have hn (g : Jₛ) : 0 < n g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hcn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F S).continuous)
  have hcont : Continuous (fun gx : Jₛ × ℝ ↦ (n gx.1) ^ (-gx.2)) :=
    (hcn.comp continuous_fst).rpow (continuous_snd.neg) (fun gx ↦ Or.inl (hn gx.1).ne')
  obtain ⟨D, hD⟩ := (hK.prod (isCompact_Icc (a := lo) (b := hi))).bddAbove_image hcont.continuousOn
  refine ⟨max 0 D, le_max_left _ _, fun g hg z hz ↦ ?_⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hn g), Complex.neg_re]
  exact (hD ⟨(g, z.re), ⟨hg, hz⟩, rfl⟩).trans (le_max_right _ _)

/-- Paper: Theorem 7.1.2.3, pp. 317–323. Above a fixed height the true weighted Mellin
integrand decays to arbitrary polynomial order on a common circle about each strip pole,
uniformly over a compact set of ideles for each fixed test.
Deviation: The punctured disk isolates a whole pole, including all of its principal part. -/
theorem sLocalStripPoles_mellin_circle_decay_of_same_prime
    (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (f : Tests) (K : Set Jₛ) (hK : IsCompact K) (N : ℕ) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| →
      ∀ g ∈ K,
      (∀ z ∈ Metric.closedBall a.val r, z ≠ a.val →
        AnalyticAt ℂ (fun s ↦ ((((normₛ g).val : ℝ) : ℂ) ^ (-s)) * Z(f,χ,s)) z) ∧
      ∀ z ∈ Metric.sphere a.val r,
        ‖((((normₛ g).val : ℝ) : ℂ) ^ (-z)) * Z(f,χ,z)‖ ≤ C / (1 + |a.val.im|) ^ N := by
  classical
  obtain ⟨η, he, heq, _⟩ := sLocal_character_extension χ
  obtain ⟨r, hr, ε, hε, hgeom⟩ := sLocalFinitePoles_isolating_circles χ η hsame
  obtain ⟨H, hhigh⟩ := sLocalStripPoles_high_finite_place χ A
  obtain ⟨D, hD, hkernel⟩ := sLocalNormPower_bounded_on_compact_strip K hK (-1) 1
  obtain ⟨L, hL, Y, htail⟩ := RiemannMasullo.sLocalIdelicZFunction_cleared_strip_tails χ η f he heq (-1) 1 N
  refine ⟨r, hr.1, (D * (2 : ℝ) ^ N) * (L / ε), by positivity, max H (max (Y+1) 3), ?_⟩
  intro a ha g hg
  obtain ⟨har, hreg, hcircle⟩ := hgeom a.val (hhigh a ((le_max_left _ _).trans_lt ha))
  constructor
  · intro z hz hne
    have hp := sLocalIdelicZFunction_poles f χ z
    rw [min_eq_left (hreg z hz hne)] at hp
    have hzeta := ((sLocalIdelicZFunction_meromorphic f χ) (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hp
    have hpos : 0 < ((normₛ g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    exact ((differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hpos.ne'))).analyticAt z).mul hzeta
  · intro z hz
    have hdist : ‖z - a.val‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    have hre : |z.re| ≤ r := by simpa [Complex.sub_re, har, hdist] using Complex.abs_re_le_norm (z - a.val)
    have hzre : z.re ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(abs_le.mp hre).1, hr.2],
      by linarith [(abs_le.mp hre).2, hr.2]⟩
    have him : |a.val.im| ≤ |z.im| + r := by
      calc
        |a.val.im| = |(a.val-z).im + z.im| := by rw [Complex.sub_im, sub_add_cancel]
        _ ≤ |(a.val-z).im| + |z.im| := abs_add_le _ _
        _ ≤ |z.im| + r := by linarith [Complex.abs_im_le_norm (a.val-z), norm_sub_rev a.val z]
    have hY : Y + 1 < |a.val.im| := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt ha
    have h3 : 3 < |a.val.im| := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt ha
    have hT := htail z hzre (show Y < |z.im| by linarith [hr.2])
    have hZ : |z.im| ^ N * ‖Z(f,χ,z)‖ ≤ L / ε := by
      apply (le_div_iff₀ hε).mpr
      calc
        _ = |z.im| ^ N * (ε * ‖Z(f,χ,z)‖) := by ring
        _ ≤ |z.im| ^ N * (‖P(η,z)‖ * ‖Z(f,χ,z)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hcircle z hz) (norm_nonneg _)) (by positivity)
        _ ≤ L := by simpa only [norm_mul] using hT
    have hheight : (1+|a.val.im|) ^ N ≤ (2 : ℝ)^N * |z.im|^N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith [hr.2]) N
    apply (le_div_iff₀ (pow_pos (by positivity) N)).mpr
    rw [norm_mul]
    calc
      _ ≤ (D * ‖Z(f,χ,z)‖) * ((2 : ℝ)^N * |z.im|^N) := mul_le_mul
        (mul_le_mul_of_nonneg_right (hkernel g hg z hzre) (norm_nonneg _)) hheight
        (by positivity) (mul_nonneg hD (norm_nonneg _))
      _ = (D * (2 : ℝ)^N) * (|z.im|^N * ‖Z(f,χ,z)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by positivity)

/-- Paper: Theorem 7.1.2.3, pp. 317–323. At one rational prime the actual residue term
decays to every polynomial order in the height of a strip pole, uniformly on a compact
set of ideles for a fixed Schwartz–Bruhat test.
Deviation: A residue includes the full contribution of a pole of any multiplicity. -/
private theorem sLocalStripPoles_weighted_residue_decay_of_same_prime
    (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (f : Tests) (K : Set Jₛ) (hK : IsCompact K) (N : ℕ) :
    ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| → ∀ g ∈ K,
      ‖star (χ g : ℂ) * complexResidue (fun z ↦ ((((normₛ g).val : ℝ) : ℂ) ^ (-z)) *
        Z(f,χ,z)) a.val‖ ≤ C / (1 + |a.val.im|) ^ N := by
  obtain ⟨r, hr, C, hC, T, hc⟩ := sLocalStripPoles_mellin_circle_decay_of_same_prime
    χ A hsame f K hK N
  refine ⟨r*C, mul_nonneg hr.le hC, T, fun a ha g hg ↦ ?_⟩
  obtain ⟨hreg, hcircle⟩ := hc a ha g hg
  rw [norm_mul, norm_star, Circle.norm_coe, one_mul]
  simpa only [mul_div_assoc] using norm_complexResidue_le_circle hr hreg hcircle

/-- A fixed Mellin residue is bounded over a compact set of ideles, at any center. -/
private theorem sLocal_weighted_residue_bounded_at (χ : PontryaginDual Jₛ) (f : Tests)
    (K : Set Jₛ) (hK : IsCompact K) (a : ℂ) :
    ∃ B ≥ (0 : ℝ), ∀ g ∈ K, ‖star (χ g : ℂ) * complexResidue
      (fun z ↦ ((((normₛ g).val : ℝ) : ℂ) ^ (-z)) * Z(f,χ,z)) a‖ ≤ B := by
  have hm := ((sLocalIdelicZFunction_meromorphic f χ) (mem_univ a)).meromorphicAt
  obtain ⟨R, hR, h⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hm.eventually_analyticAt
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hZ (z : ℂ) (hz : z ∈ Metric.closedBall a r) (hne : z ≠ a) :
      AnalyticAt ℂ (fun s ↦ Z(f,χ,s)) z :=
    h ⟨Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hrR), hne⟩
  have hcon : ContinuousOn (fun z ↦ Z(f,χ,z)) (Metric.sphere a r) := by
    intro z hz
    apply (hZ z (Metric.sphere_subset_closedBall hz) ?_).continuousAt.continuousWithinAt
    intro hza
    have hd := Metric.mem_sphere.mp hz
    rw [hza, dist_self] at hd
    exact hr.ne' hd.symm
  obtain ⟨M, hM⟩ := (isCompact_sphere a r).bddAbove_image hcon.norm
  obtain ⟨D, hD, hk⟩ := sLocalNormPower_bounded_on_compact_strip K hK (a.re-r) (a.re+r)
  refine ⟨r * (D * max 0 M), by positivity, fun g hg ↦ ?_⟩
  rw [norm_mul, norm_star, Circle.norm_coe, one_mul]
  apply norm_complexResidue_le_circle hr
  · intro z hz hne
    have hpos : 0 < ((normₛ g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    exact ((differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hpos.ne'))).analyticAt z).mul
      (hZ z hz hne)
  · intro z hz
    have hd : ‖z-a‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    have hdre := Complex.abs_re_le_norm (z-a)
    rw [Complex.sub_re, hd, abs_le] at hdre
    rw [norm_mul]
    exact mul_le_mul (hk g hg z ⟨by linarith [hdre.1], by linarith [hdre.2]⟩)
      ((hM ⟨z, hz, rfl⟩).trans (le_max_right _ _)) (norm_nonneg _) hD

/-- Extend a compact-set residue estimate above a height cutoff to every strip pole. -/
private theorem sLocalStripPoles_weighted_residue_bound_of_decay
    (χ : PontryaginDual Jₛ) (A : ℝ)
    (f : Tests) (K : Set Jₛ) (hK : IsCompact K) (N : ℕ)
    (htail : ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| → ∀ g ∈ K,
      ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|) ^ N) :
    ∃ C ≥ (0 : ℝ), ∀ a : strip(χ,A), ∀ g ∈ K,
      ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|) ^ N := by
  classical
  obtain ⟨L, hL, T, htail⟩ := htail
  let low := {a : strip(χ,A) | |a.val.im| ≤ T}
  have hlow : low.Finite := by
    simpa only [low, not_lt] using
      (eventually_cofinite.mp (eventually_sLocalStripPoles_abs_im_gt χ A T))
  choose B _ hB using fun a : strip(χ,A) ↦ sLocal_weighted_residue_bounded_at χ f K hK a.val
  obtain ⟨D, hD⟩ := (hlow.image (fun a : strip(χ,A) ↦ B a * (1 + |a.val.im|)^N)).bddAbove
  refine ⟨max L D, hL.trans (le_max_left _ _), fun a g hg ↦ ?_⟩
  by_cases ht : T < |a.val.im|
  · exact (htail a ht g hg).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  · apply (le_div_iff₀ (pow_pos (by positivity) N)).mpr
    exact (mul_le_mul_of_nonneg_right (hB a g hg) (by positivity)).trans
      ((hD ⟨a, le_of_not_gt ht, rfl⟩).trans (le_max_right _ _))

private theorem unitaryChart_normTwist_add (χ : PontryaginDual Jₛ) (a z : ℂ) :
    twistₛ (chart(χ) a) z = chart(χ) (z + a) := by
  ext1 g
  let n : ℂ := (((normₛ g).val : ℝ) : ℂ)
  change (χ g : ℂ) * n ^ a * n ^ z = (χ g : ℂ) * n ^ (z + a)
  rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (normₛ g).ne_zero)), mul_assoc]

private theorem complexResidue_add_center (V : ℂ → ℂ) (a : ℂ) :
    complexResidue (fun z ↦ V (z + a)) 0 = complexResidue V a := by
  simp only [complexResidue, circleIntegral, deriv_circleMap]
  simp only [circleMap, zero_add, add_comm _ a]

private theorem exists_sLocalMellinPoleTerm_continuousLinearMap (χ : PontryaginDual Jₛ) (a : ℂ) (g : Jₛ) :
    ∃ ℓ : StrongDual ℂ Tests, ∀ f, ℓ f = sLocalMellinPoleTerm χ f g a := by
  obtain ⟨u, hu⟩ := (QuotientGroup.mk_surjective g⁻¹)
  let T : Tests →L[ℂ] Tests :=
    ⟨unitTranslateEnd u, continuous_sAdeleSchwartz_unitTranslate.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨(sLocalPrincipalPartCoeff (chart(χ) a) 1).comp T, fun f ↦ ?_⟩
  let r : ℝ := (normₛ g).val
  let W (z : ℂ) := (r : ℂ) ^ (-z) * sLocalIdelicZFunction f (chart(χ) z)
  have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hW : MeromorphicAt W a :=
    ((differentiable_neg.const_cpow (c := (r : ℂ))
      (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))).analyticAt a).meromorphicAt.mul
      ((sLocalIdelicZFunction_meromorphic f χ) (mem_univ a)).meromorphicAt
  have hunit (z : ℂ) : chart(χ) z g⁻¹ = star (χ g : ℂ) * (r : ℂ) ^ (-z) := by
    rw [map_inv]
    change ((χ g : ℂ) * (r : ℂ) ^ z)⁻¹ = _
    rw [mul_inv, Complex.cpow_neg, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
    rfl
  change sLocalZLaurentCoeff (schwartzBruhatUnitTranslate u f) (chart(χ) a) (- (1 : ℤ)) = _
  unfold sLocalZLaurentCoeff
  simp only [neg_add_cancel, zpow_zero, div_one]
  have hshift := unitaryChart_normTwist_add χ a
  simp_rw [hshift]
  rw [complexResidue_add_center (fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f) (chart(χ) z)) a]
  have hfun : (fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f) (chart(χ) z)) =
      fun z ↦ star (χ g : ℂ) * W z + 0 := by
    funext z
    rw [sLocalPrincipalPartCoeff_translate_zeta, hu, hunit]
    simp only [W, add_zero, mul_assoc]
  rw [hfun, complexResidue_const_mul_add (G := fun _ ↦ 0) (star (χ g : ℂ)) hW analyticAt_const.meromorphicAt]
  have hz : complexResidue (fun _ ↦ (0 : ℂ)) a = 0 :=
    complexResidue_zero_of_analytic_germ (H := fun _ ↦ 0) analyticAt_const (.of_forall fun _ ↦ rfl)
  rw [hz, add_zero]
  rfl

private theorem strongDual_family_bounded_on_bounded_set {X ι : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [PolynormableSpace ℂ X] [BarrelledSpace ℂ X]
    (L : ι → StrongDual ℂ X) (hb : ∀ x, ∃ C : ℝ, ∀ i, ‖L i x‖ ≤ C)
    {B : Set X} (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C : ℝ, ∀ i, ∀ x ∈ B, ‖L i x‖ ≤ C := by
  have hpoint (x : X) : Bornology.IsVonNBounded ℂ (range fun i ↦ L i x) := by
    obtain ⟨C, hC⟩ := hb x
    exact (NormedSpace.isVonNBounded_iff' ℂ).2 ⟨C, forall_mem_range.mpr hC⟩
  have heq := PolynormableSpace.banach_steinhaus (𝓕 := L) hpoint
  obtain ⟨q, hq, hle⟩ := (norm_withSeminorms ℂ ℂ).uniformEquicontinuous_iff_exists_continuous_seminorm
    (fun i ↦ (L i).toLinearMap) |>.mp heq ()
  obtain ⟨C, _, hC⟩ := (PolynormableSpace.withSeminorms ℂ X).isVonNBounded_iff_seminorm_bounded.mp
    hB ⟨q, hq⟩
  exact ⟨C, fun i x hx ↦ (hle i x).trans (hC x hx).le⟩

/-- Uniform boundedness upgrades decay for each test on a compact set of idèles to decay
uniform over any bounded set of tests. -/
private theorem sLocalMellinPoleTerm_bounded_compact_of_decay (χ : PontryaginDual Jₛ) (A : ℝ)
    (B : Set Tests) (hB : Bornology.IsVonNBounded ℂ B) (K : Set Jₛ) (hK : IsCompact K) (N : ℕ)
    (hdecay : ∀ f : Tests, ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A),
      T < |a.val.im| → ∀ g ∈ K, ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|) ^ N) :
    ∃ C ≥ (0 : ℝ), ∀ a : strip(χ,A), ∀ f ∈ B, ∀ g ∈ K,
      ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|) ^ N := by
  classical
  let : BarrelledSpace ℂ Tests := (sAdeleSchwartz_montel (F := F) S).1
  let I := strip(χ,A) × K
  let h (i : I) : ℝ := (1 + |i.1.val.im|) ^ N
  have hpos (i : I) : 0 < h i := by dsimp only [h]; positivity
  choose R hR using fun i : I ↦ exists_sLocalMellinPoleTerm_continuousLinearMap χ i.1.val i.2.val
  let weighted (i : I) : StrongDual ℂ Tests := (h i : ℂ) • R i
  have hU (i : I) (f : Tests) : ‖weighted i f‖ = h i * ‖sLocalMellinPoleTerm χ f i.2.val i.1.val‖ := by
    simp only [weighted, smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos i), hR]
  have hb (f : Tests) : ∃ C : ℝ, ∀ i : I, ‖weighted i f‖ ≤ C := by
    obtain ⟨C, _, hC⟩ := sLocalStripPoles_weighted_residue_bound_of_decay χ A f K hK N (hdecay f)
    refine ⟨C, fun i ↦ ?_⟩
    rw [hU, mul_comm]
    exact (le_div_iff₀ (hpos i)).mp (hC i.1 i.2.val i.2.property)
  obtain ⟨C, hC⟩ := strongDual_family_bounded_on_bounded_set weighted hb hB
  refine ⟨max C 0, le_max_right _ _, fun a f hf g hg ↦ ?_⟩
  let i : I := (a, ⟨g, hg⟩)
  apply (le_div_iff₀ (hpos i)).mpr
  change ‖sLocalMellinPoleTerm χ f i.2.val i.1.val‖ * h i ≤ _
  rw [mul_comm, ← hU]
  exact (hC i f hf).trans (le_max_left _ _)

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. At every one-prime strip pole the complete
Mellin residue decays to every polynomial order, simultaneously over a bounded set of
Schwartz–Bruhat tests and a compact set of idèles. -/
theorem sLocalSinglePrime_residue_bound_on_bounded_compact (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (B : Set Tests) (hB : Bornology.IsVonNBounded ℂ B) (K : Set Jₛ) (hK : IsCompact K) (N : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ a : strip(χ,A), ∀ f ∈ B, ∀ g ∈ K,
      ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|) ^ N :=
  sLocalMellinPoleTerm_bounded_compact_of_decay χ A B hB K hK N
    (fun f ↦ sLocalStripPoles_weighted_residue_decay_of_same_prime χ A hsame f K hK N)

/-- The unconditional sum of the actual Mellin residues assigned to a given place or block. -/
def sLocalAssignedMellinPoleSum {ι : Type*} (χ : PontryaginDual Jₛ) (A : ℝ)
    (assign : ℂ → ι) (v : ι) (f : Tests) (g : Jₛ) : ℂ :=
  ∑' a : strip(χ,A), if assign a.val = v then sLocalMellinPoleTerm χ f g a.val else 0

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. Inverse-square residue bounds on compact idèle sets
for each individual test give absolute convergence for every assignment.
The residue sums and the sums of their norms converge uniformly on products of bounded
test sets and compact idèle sets as the two window heights tend independently to infinity. -/
theorem sLocalMellinPoleTerm_separatePlace_absolute_of_residue_decay {ι : Type*}
    (χ : PontryaginDual Jₛ) (A : ℝ)
    (hdecay : ∀ (f : Tests) (K : Set Jₛ), IsCompact K →
      ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| → ∀ g ∈ K,
        ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|) ^ 2)
    (assign : ℂ → ι) :
    (∀ f g, Summable (fun a : strip(χ,A) ↦ ‖sLocalMellinPoleTerm χ f g a.val‖)) ∧
    ∀ (v : ι) (B : Set Tests), Bornology.IsVonNBounded ℂ B → ∀ K : Set Jₛ, IsCompact K →
      TendstoUniformlyOn (fun h fg ↦ ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v),
        sLocalMellinPoleTerm χ fg.1 fg.2 a)
        (fun fg ↦ sLocalAssignedMellinPoleSum χ A assign v fg.1 fg.2) (atBot ×ˢ atTop) (B ×ˢ K) ∧
      TendstoUniformlyOn (fun h fg ↦ ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v),
        ‖sLocalMellinPoleTerm χ fg.1 fg.2 a‖)
        (fun fg ↦ ∑' a : strip(χ,A),
          if assign a.val = v then ‖sLocalMellinPoleTerm χ fg.1 fg.2 a.val‖ else 0)
        (atBot ×ˢ atTop) (B ×ˢ K) := by
  let w (a : strip(χ,A)) := 1 / (1 + |a.val.im|) ^ 2
  have hw : Summable w := summable_sLocalStripPoles_inv_height_sq_all χ A
  constructor
  · intro f g
    obtain ⟨C, _, hC⟩ := sLocalStripPoles_weighted_residue_bound_of_decay
      χ A f {g} isCompact_singleton 2 (hdecay f {g} isCompact_singleton)
    refine (hw.mul_left C).of_norm_bounded ?_
    intro a
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [w, div_eq_mul_inv, one_mul] using hC a g (mem_singleton g)
  · intro v B hB K hK
    obtain ⟨C, _, hC⟩ := sLocalMellinPoleTerm_bounded_compact_of_decay
      χ A B hB K hK 2 (fun f ↦ hdecay f K hK)
    let M (a : strip(χ,A)) := C * w a
    have hM : Summable M := hw.mul_left C
    have hb (a : strip(χ,A)) (fg : Tests × Jₛ) (hfg : fg ∈ B ×ˢ K) :
        ‖sLocalMellinPoleTerm χ fg.1 fg.2 a.val‖ ≤ M a := by
      simpa only [M, w, div_eq_mul_inv, one_mul] using hC a fg.1 hfg.1 fg.2 hfg.2
    have he : MeromorphicOn (fun z ↦ sLocalRhoFactor (chart(χ) z)) (Complex.re ⁻¹' Ioo (-A - 1) 2) :=
      (sLocalRhoFactor_meromorphic χ).meromorphicOn
    constructor
    · simpa only [sLocalStripPoleWindow, sLocalAssignedMellinPoleSum] using
        tendstoUniformlyOn_separatePlacePartialSum_of_cofinite_bound
        (a := -A-1) (b := 2) (σ₁ := -A) (σ₂ := 1) he (by linarith) (by norm_num)
        assign (fun a fg ↦ sLocalMellinPoleTerm χ fg.1 fg.2 a) (B ×ˢ K) M hM (.of_forall hb) v
    · have hn (a : strip(χ,A)) (fg : Tests × Jₛ) (hfg : fg ∈ B ×ˢ K) :
          ‖‖sLocalMellinPoleTerm χ fg.1 fg.2 a.val‖‖ ≤ M a :=
        (Real.norm_of_nonneg (norm_nonneg _)).le.trans (hb a fg hfg)
      simpa only [sLocalStripPoleWindow] using
        tendstoUniformlyOn_separatePlacePartialSum_of_cofinite_bound
          (a := -A-1) (b := 2) (σ₁ := -A) (σ₂ := 1) he (by linarith) (by norm_num)
          assign (fun a fg ↦ ‖sLocalMellinPoleTerm χ fg.1 fg.2 a‖) (B ×ˢ K) M hM (.of_forall hn) v

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323; absolute sums on p. 389. For a single
residue characteristic, the full weighted residues are absolutely summable over all strip
poles. For every assignment both the complex sums and the sums of their norms converge
uniformly on each product of a bounded set of tests and a compact set of idèles, with the
upper and lower heights tending independently to infinity. -/
theorem sLocalSinglePrime_separatePlace_absolute {ι : Type*}
    (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) (assign : ℂ → ι) :
    (∀ f g, Summable (fun a : strip(χ,A) ↦ ‖sLocalMellinPoleTerm χ f g a.val‖)) ∧
    ∀ (v : ι) (B : Set Tests), Bornology.IsVonNBounded ℂ B → ∀ K : Set Jₛ, IsCompact K →
      TendstoUniformlyOn (fun h fg ↦ ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v),
        sLocalMellinPoleTerm χ fg.1 fg.2 a)
        (fun fg ↦ sLocalAssignedMellinPoleSum χ A assign v fg.1 fg.2) (atBot ×ˢ atTop) (B ×ˢ K) ∧
      TendstoUniformlyOn (fun h fg ↦ ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v),
        ‖sLocalMellinPoleTerm χ fg.1 fg.2 a‖)
        (fun fg ↦ ∑' a : strip(χ,A),
          if assign a.val = v then ‖sLocalMellinPoleTerm χ fg.1 fg.2 a.val‖ else 0)
        (atBot ×ˢ atTop) (B ×ˢ K) :=
  sLocalMellinPoleTerm_separatePlace_absolute_of_residue_decay χ A
    (fun f K hK ↦ sLocalStripPoles_weighted_residue_decay_of_same_prime χ A hsame f K hK 2) assign

/-- The coefficient of order `-(j+1)` at the chart center is the residue of the zeta
integral multiplied by the corresponding nonnegative power of the centered variable. -/
private theorem sLocalZLaurentCoeff_neg_succ_eq_residue (χ : PontryaginDual Jₛ) (f : Tests)
    (a : ℂ) (j : ℕ) :
    sLocalZLaurentCoeff f (chart(χ) a) (-(j.succ : ℤ)) =
      complexResidue (fun z ↦ (z-a)^j * sLocalIdelicZFunction f (chart(χ) z)) a := by
  have hshift := unitaryChart_normTwist_add χ a
  unfold sLocalZLaurentCoeff
  rw [← complexResidue_add_center (fun z ↦ (z-a)^j * sLocalIdelicZFunction f (chart(χ) z)) a]
  congr 1
  funext z
  simp [hshift, zpow_neg, div_eq_mul_inv, mul_comm]

/-- Paper: Definition 7.1.2.1, p. 316, and (8.4.0.2), p. 389. Each principal Laurent
coefficient of fixed order decays to all polynomial orders along the high strip poles
above one rational prime.
Deviation: Principal coefficients have negative Laurent indices. -/
theorem sLocalZLaurentCoeff_neg_decay_of_same_prime (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (f : Tests) (k N : ℕ) (hk : 0 < k) :
    ∃ D ≥ (0 : ℝ), ∀ᶠ a : strip(χ,A) in cofinite,
      ‖sLocalZLaurentCoeff f (chart(χ) a.val) (-(k : ℤ))‖ ≤ D / (1 + |a.val.im|)^N := by
  classical
  cases k with
  | zero => exact (Nat.lt_irrefl _ hk).elim
  | succ j =>
    obtain ⟨r, hr, C, hC, T, h⟩ := sLocalStripPoles_mellin_circle_decay_of_same_prime χ A hsame
      f {1} isCompact_singleton N
    refine ⟨r * r^j * C, by positivity, ?_⟩
    filter_upwards [eventually_sLocalStripPoles_abs_im_gt χ A T] with a ha
    obtain ⟨hreg, hcircle⟩ := h a ha 1 (mem_singleton _)
    have hZ (z : ℂ) (hz : z ∈ Metric.closedBall a.val r) (hne : z ≠ a.val) :
        AnalyticAt ℂ (fun s ↦ sLocalIdelicZFunction f (chart(χ) s)) z := by
      simpa using hreg z hz hne
    have hZc (z : ℂ) (hz : z ∈ Metric.sphere a.val r) :
        ‖sLocalIdelicZFunction f (chart(χ) z)‖ ≤ C / (1 + |a.val.im|)^N := by
      simpa using hcircle z hz
    rw [sLocalZLaurentCoeff_neg_succ_eq_residue]
    calc
      _ ≤ r * (r^j * (C / (1 + |a.val.im|)^N)) := by
        apply norm_complexResidue_le_circle hr
        · intro z hz hne
          exact ((analyticAt_id.sub analyticAt_const).pow j).mul (hZ z hz hne)
        · intro z hz
          have hd : ‖z-a.val‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
          rw [norm_mul, norm_pow, hd]
          exact mul_le_mul_of_nonneg_left (hZc z hz) (by positivity)
      _ = _ := by ring

/-- Paper: Equation (8.4.0.2), p. 389. When the finite places lie over a single rational
prime, the absolute values of each fixed principal Laurent coefficient are summable over
all distinct strip poles for every Schwartz–Bruhat test.
Deviation: The coefficient of the term of logarithmic degree `k-1` has Laurent index `-k`. -/
theorem summable_sLocalZLaurentCoeff_neg_of_same_prime (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (f : Tests) (k : ℕ) (hk : 0 < k) :
    Summable (fun a : strip(χ,A) ↦ ‖sLocalZLaurentCoeff f (chart(χ) a.val) (-(k : ℤ))‖) := by
  obtain ⟨C, _, hc⟩ := sLocalZLaurentCoeff_neg_decay_of_same_prime χ A hsame f k 2 hk
  apply ((summable_sLocalStripPoles_inv_height_sq χ A hsame).mul_left C).of_norm_bounded_eventually
  filter_upwards [hc] with a ha
  simpa [div_eq_mul_inv] using ha

end

/-! ## Common-height contour on an admissible left line -/

section CommonHeightContour

local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "P(" η "," z ")" => ∏ v : S, (finiteHeckeEulerFactor η v.val z)⁻¹
local notation "Z(" f "," χ "," z ")" => sLocalIdelicZFunction f (chart(χ) z)
local notation "vz(" σ "," y ")" => ((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I

private theorem euler_reciprocal_lower_on_line (η : U) (σ : ℝ) (hσ : σ ≠ 0) :
    ∃ c > (0 : ℝ), ∀ y : ℝ, c ≤ ‖P(η,vz(σ,y))‖ := by
  classical
  let c (v : S) : ℝ := min 1 |1 - (v.val.asIdeal.absNorm : ℝ) ^ (-σ)|
  have hq (v : S) : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hpos (v : S) : 0 < c v := by
    apply lt_min one_pos (abs_pos.mpr (sub_ne_zero.mpr ?_))
    rcases lt_or_gt_of_ne hσ with hs | hs
    · exact (Real.one_lt_rpow (hq v) (neg_pos.mpr hs)).ne
    · exact (Real.rpow_lt_one_of_one_lt_of_neg (hq v) (neg_neg_of_pos hs)).ne'
  refine ⟨∏ v, c v, Finset.prod_pos (fun v _ ↦ hpos v), fun y ↦ ?_⟩
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun v _ ↦ (hpos v).le)
  intro v _
  unfold finiteHeckeEulerFactor
  split_ifs
  · rw [inv_inv]
    apply (min_le_right _ _).trans
    have h := abs_norm_sub_norm_le (1 : ℂ)
      ((ideleClassNormTwist η 0).localValue v.val * (v.val.asIdeal.absNorm : ℂ) ^ (-(vz(σ,y))))
    rw [norm_one, norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans (hq v))] at h
    simpa using h
  · simpa only [inv_one, norm_one] using min_le_left (1 : ℝ) _

private theorem normPower_mul_verticalIntegrable_of_order
    (χ : PontryaginDual Jₛ) (f : Tests) (r : ℝ) (hr : 0 < r) (σ : ℝ) (hσ : σ ≠ 0)
    (hreg : ∀ y : ℝ, 0 ≤ meromorphicOrderAt (fun z ↦ Z(f,χ,z)) (vz(σ,y))) :
    Complex.VerticalIntegrable (fun z ↦ (r : ℂ) ^ (-z) * Z(f,χ,z)) σ := by
  obtain ⟨η, he, heq, -⟩ := sLocal_character_extension χ
  obtain ⟨C, hC, T, htail⟩ := sLocalIdelicZFunction_cleared_strip_tails χ η f he heq σ σ 2
  obtain ⟨c, hc, hP⟩ := euler_reciprocal_lower_on_line (S := S) η σ hσ
  let trace (y : ℝ) := (r : ℂ) ^ (-(vz(σ,y))) * Z(f,χ,vz(σ,y))
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have htrace : Continuous trace := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hf := ((sLocalIdelicZFunction_meromorphic f χ) (mem_univ (vz(σ,y)))).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hreg y)
    have hu : AnalyticAt ℂ (fun z : ℂ ↦ (r : ℂ)^(-z)) (vz(σ,y)) :=
      (differentiable_neg.const_cpow (Or.inl hrC)).analyticAt _
    exact ContinuousAt.comp (g := fun z ↦ (r : ℂ)^(-z) * Z(f,χ,z)) (f := fun x : ℝ ↦ vz(σ,x)) (hu.mul hf).continuousAt (by fun_prop)
  change Integrable trace
  apply htrace.locallyIntegrable.integrable_of_isBigO_cocompact _
    (integrable_inv_one_add_sq.integrableAtFilter _)
  rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop]
  apply Asymptotics.IsBigO.of_bound (2 * (r ^ (-σ) * C / c))
  have hylarge : ∀ᶠ y : ℝ in comap abs atTop, max T 1 < |y| :=
    tendsto_comap.eventually_gt_atTop _
  filter_upwards [hylarge] with y hy
  have h₁ : 1 < |y| := (le_max_right T 1).trans_lt hy
  have hT : T < |y| := (le_max_left T 1).trans_lt hy
  have hb := htail (vz(σ,y)) (by simp) (by simpa using hT)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add, norm_mul] at hb
  have hsize : |y|^2 * ‖Z(f,χ,vz(σ,y))‖ ≤ C / c := by
    apply (le_div_iff₀ hc).mpr
    calc
      |y|^2 * ‖Z(f,χ,vz(σ,y))‖ * c ≤ |y|^2 * ‖Z(f,χ,vz(σ,y))‖ * ‖P(η,vz(σ,y))‖ :=
        mul_le_mul_of_nonneg_left (hP y) (by positivity)
      _ = _ := by ring
      _ ≤ _ := hb
  have hy2 : 1 ≤ y^2 := by rw [← sq_abs]; exact one_le_pow₀ h₁.le
  have hpow : ‖(r : ℂ)^(-(vz(σ,y)))‖ = r^(-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp
  simp only [trace, norm_mul, hpow, Real.norm_of_nonneg (by positivity : 0 ≤ (1 + y^2)⁻¹)]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + y^2)).mpr
  have hscale := mul_le_mul_of_nonneg_left hsize (Real.rpow_nonneg hr.le (-σ))
  rw [sq_abs] at hscale
  rw [mul_div_assoc]
  calc
    _ ≤ (r ^ (-σ) * ‖Z(f,χ,vz(σ,y))‖) * (2 * y ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * (r ^ (-σ) * (y ^ 2 * ‖Z(f,χ,vz(σ,y))‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)

private theorem nonpole_on_large_euler_lines
    (χ : PontryaginDual Jₛ) (η : U) (f : Tests)
    (h : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist η 0,h⟩ = chart(χ) 0)
    (a b : ℝ) :
    ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T < |z.im| → P(η,z) ≠ 0 →
      0 ≤ meromorphicOrderAt (fun z ↦ Z(f,χ,z)) z := by
  obtain ⟨C, _, T, hbound⟩ := sLocalIdelicZFunction_cleared_strip_tails χ η f h he (a-1) (b+1) 0
  refine ⟨T, fun z hz ht hP ↦ ?_⟩
  by_contra! ho
  have hc := norm_pos_iff.mpr hP
  let c := ‖P(η,z)‖/2
  have hc' : 0 < c := half_pos hc
  have hr : ∀ᶠ w : ℂ in 𝓝 z, a-1 < w.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show a-1 < z.re by linarith [hz.1])
  have hr' : ∀ᶠ w : ℂ in 𝓝 z, w.re < b+1 := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (show z.re < b+1 by linarith [hz.2])
  have ht' : ∀ᶠ w : ℂ in 𝓝 z, T < |w.im| := (isOpen_lt continuous_const Complex.continuous_im.abs).mem_nhds ht
  have hpcont : Continuous (fun w : ℂ ↦ P(η,w)) := by
    classical
    apply continuous_finsetProd
    intro v _
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp only [inv_inv]
      have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        ((Ideal.absNorm_eq_zero_iff).not.mpr v.val.ne_bot)
      exact continuous_const.sub (continuous_const.mul (continuous_neg.const_cpow (Or.inl hq)))
    · exact continuous_const
  have hcnear : ∀ᶠ w : ℂ in 𝓝 z, c < ‖P(η,w)‖ :=
    (isOpen_lt continuous_const hpcont.norm).mem_nhds (half_lt_self hc)
  have hover := (tendsto_norm_atTop_iff_cobounded.mpr (tendsto_cobounded_of_meromorphicOrderAt_neg ho)).eventually_gt_atTop (C/c)
  obtain ⟨w, ⟨hrw, hrw', htw, hcw⟩, hw⟩ :=
    (((hr.and (hr'.and (ht'.and hcnear))).filter_mono nhdsWithin_le_nhds).and hover).exists
  have hsmall := hbound w ⟨hrw.le, hrw'.le⟩ htw
  simp only [pow_zero, one_mul, norm_mul] at hsmall
  have hbig := (div_lt_iff₀ hc').mp hw
  exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hcw.le (norm_nonneg _)).trans hsmall))
    (by simpa only [mul_comm c] using hbig)

private theorem contour_horizontal_tendsto
    (χ : PontryaginDual Jₛ) (η : U) (f : Tests)
    (h : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist η 0,h⟩ = chart(χ) 0)
    (r : ℝ) (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (t : ℕ → ℝ) (ht : Tendsto (fun n ↦ |t n|) atTop atTop)
    (c : ℝ) (hc : 0 < c) (hP : ∀ n : ℕ, ∀ x ∈ Icc a b, c ≤ ‖P(η,vz(x,t n))‖) :
    Tendsto (fun n ↦ ∫ x in a..b, (r : ℂ)^(-(vz(x,t n))) * Z(f,χ,vz(x,t n))) atTop (𝓝 0) := by
  obtain ⟨C, _, T, htail⟩ := sLocalIdelicZFunction_cleared_strip_tails χ η f h he a b 1
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun x : ℝ ↦ r^(-x)) (s := Icc a b) (by fun_prop (disch := positivity))
  have hDn : 0 ≤ D := (norm_nonneg _).trans (hD a ⟨le_rfl, hab⟩)
  apply squeeze_zero_norm' (a := fun n : ℕ ↦ (D * (C / c) * |b-a|) / |t n|) _
    (ht.const_div_atTop _)
  filter_upwards [ht.eventually_gt_atTop (max T 0)] with n hn
  have htn : 0 < |t n| := (le_max_right T 0).trans_lt hn
  have hpoint (x : ℝ) (hx : x ∈ uIcc a b) :
      ‖(r : ℂ)^(-(vz(x,t n))) * Z(f,χ,vz(x,t n))‖ ≤ D * (C/c) / |t n| := by
    rw [uIcc_of_le hab] at hx
    have hpow : ‖(r : ℂ)^(-(vz(x,t n)))‖ = r^(-x) := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp
    have hDX : r^(-x) ≤ D := (le_abs_self _).trans (hD x hx)
    have hb := htail (vz(x,t n)) (by simpa using hx) (by simpa using (le_max_left T 0).trans_lt hn)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
      zero_add, pow_one, norm_mul] at hb
    have hsize : ‖Z(f,χ,vz(x,t n))‖ * |t n| ≤ C/c := by
      apply (le_div_iff₀ hc).mpr
      calc
        _ ≤ ‖Z(f,χ,vz(x,t n))‖ * |t n| * ‖P(η,vz(x,t n))‖ :=
          mul_le_mul_of_nonneg_left (hP n x hx) (by positivity)
        _ = _ := by ring
        _ ≤ _ := hb
    rw [norm_mul, hpow]
    apply (le_div_iff₀ htn).mpr
    rw [mul_assoc]
    exact mul_le_mul hDX hsize (by positivity) hDn
  calc
    _ ≤ _ := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (fun x hx ↦ hpoint x (uIoc_subset_uIcc hx))
    _ = _ := by ring

private theorem reciprocal_euler_upper_on_halfPlane (η : U) (W : Finset (HeightOneSpectrum (𝓞 F))) (a : ℝ) :
    ∃ D > (0 : ℝ), ∀ z : ℂ, a ≤ z.re → ‖reciprocalPartialHeckeEulerProduct η W z‖ ≤ D := by
  classical
  let m (v : HeightOneSpectrum (𝓞 F)) := 1 + (v.asIdeal.absNorm : ℝ) ^ (-a)
  have hq (v : HeightOneSpectrum (𝓞 F)) : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hpos (v : HeightOneSpectrum (𝓞 F)) : 0 < m v :=
    add_pos one_pos (Real.rpow_pos_of_pos (zero_lt_one.trans (hq v)) _)
  refine ⟨∏ v ∈ W, m v, Finset.prod_pos (fun v _ ↦ hpos v), fun z hz ↦ ?_⟩
  rw [reciprocalPartialHeckeEulerProduct, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
  intro v _
  unfold finiteHeckeEulerFactor
  split_ifs
  · rw [inv_inv]
    apply (norm_sub_le _ _).trans
    rw [norm_one, norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans (hq v))]
    exact add_le_add_right (Real.rpow_le_rpow_of_exponent_le (hq v).le (by simpa using neg_le_neg hz)) _
  · simpa [m] using (Real.rpow_nonneg (zero_lt_one.trans (hq v)).le (-a))

private theorem exists_sLocal_contour_heights (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A) :
    ∃ (η : U) (hη : ideleClassNormTwist η 0 ∈ unramifiedOutside F S),
      sIdeleRestriction F S ⟨ideleClassNormTwist η 0,hη⟩ = chart(χ) 0 ∧
      ∃ (lo hi : ℕ → ℝ) (c : ℝ), 0 < c ∧ Tendsto lo atTop atBot ∧ Tendsto hi atTop atTop ∧
        ∀ n : ℕ, ∀ x ∈ Icc (-A) 1,
          c ≤ ‖P(η,vz(x,lo n))‖ ∧ c ≤ ‖P(η,vz(x,hi n))‖ := by
  classical
  obtain ⟨η, hs, he, W, hSW, hW⟩ := sLocal_character_extension χ
  have hw : ideleClassNormTwist η 0 ∈ unramifiedOutside F W :=
    (mem_unramifiedOutside_iff F W _).mpr fun v hv ↦ (mem_unramifiedOutside_iff F S _).mp hs v (fun hm ↦ hv (hSW hm))
  obtain ⟨c, T, hc, -, hpos, hneg, hlim, hlow⟩ :=
    exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow W hW η hw hA
  obtain ⟨D, hD, hupper⟩ := reciprocal_euler_upper_on_halfPlane η (W \ S) (-A)
  have hrow (k : ℤ) (x : ℝ) (hx : x ∈ Icc (-A) 1) : c/D ≤ ‖P(η,vz(x,T k))‖ := by
    have hlow' := hlow k x ⟨hx.1, by linarith [hx.2]⟩
    have hu := hupper (vz(x,T k)) (by simpa using hx.1)
    rw [reciprocalPartialHeckeEulerProduct, ← Finset.prod_sdiff hSW, norm_mul] at hlow'
    rw [reciprocalPartialHeckeEulerProduct] at hu
    rw [Finset.prod_coe_sort (f := fun v : HeightOneSpectrum (𝓞 F) ↦ (finiteHeckeEulerFactor η v (vz(x,T k)))⁻¹) (s := S)]
    exact (div_le_iff₀ hD).mpr
      (hlow'.trans (by simpa only [mul_comm D] using mul_le_mul_of_nonneg_right hu (norm_nonneg _)))
  have hIndex : Tendsto (fun k : ℕ ↦ (k : ℤ)) atTop (comap abs atTop) := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def, abs_of_nonneg (Int.natCast_nonneg _)] using (tendsto_natCast_atTop_atTop (R := ℤ))
  have hNegIndex : Tendsto (fun k : ℕ ↦ -(k : ℤ)) atTop (comap abs atTop) := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def, abs_neg] using tendsto_comap_iff.mp hIndex
  refine ⟨η, hs, he, fun n ↦ T (-(n:ℤ)), fun n ↦ T (n:ℤ), c/D, div_pos hc hD, ?_, ?_,
    fun n x hx ↦ ⟨hrow _ x hx, hrow _ x hx⟩⟩
  · apply (tendsto_neg_atTop_atBot.comp (hlim.comp hNegIndex)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact neg_eq_iff_eq_neg.mpr (abs_of_nonpos (hneg (-(n : ℤ)) (neg_neg_of_pos (by exact_mod_cast hn))))
  · exact (hlim.comp hIndex).congr (fun n ↦ abs_of_nonneg (hpos _ (Int.natCast_nonneg _)))

local notation "rho(" χ ")" => (fun z : ℂ ↦ sLocalRhoFactor (chart(χ) z))

open Classical in
/-- On admissible vertical sides, a common pair of escaping height sequences works
for every test and every positive norm dilation. The residue sum is over the
geometric poles of the correcting factor, with each center counted once. -/
theorem sLocalIdelicZFunction_commonHeight_residue_limit
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (rho(χ)) a) :
    ∃ lo hi : ℕ → ℝ, Tendsto lo atTop atBot ∧ Tendsto hi atTop atTop ∧
      ∀ (f : Tests) (r : ℝ), 0 < r →
        let g := fun z : ℂ ↦ (r : ℂ)^(-z) * Z(f,χ,z)
        Complex.VerticalIntegrable g (-A) ∧ Complex.VerticalIntegrable g 1 ∧
          Tendsto (fun n : ℕ ↦ ∑ a ∈ sLocalStripPoleWindow χ A (lo n, hi n), complexResidue g a) atTop
            (𝓝 ((verticalLineIntegral g 1 - verticalLineIntegral g (-A)) /
              (2 * (Real.pi : ℂ) * Complex.I))) := by
  obtain ⟨η, he, heq, lo, hi, c, hc, hlo, hhi, hP⟩ := exists_sLocal_contour_heights χ A hA
  refine ⟨lo, hi, hlo, hhi, fun f r hr ↦ ?_⟩
  let G (z : ℂ) := (r : ℂ)^(-z) * Z(f,χ,z)
  let Z₀ (z : ℂ) := Z(f,χ,z)
  let I₂ : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hI : I₂ ≠ 0 := by simp [I₂, Real.pi_ne_zero, Complex.I_ne_zero]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have unitAn (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (r : ℂ)^(-w)) z :=
    (differentiable_neg.const_cpow (Or.inl hrC)).analyticAt _
  have hZ (z : ℂ) := (sLocalIdelicZFunction_meromorphic f χ) (mem_univ z)
  have hMG (z : ℂ) : MeromorphicAt G z := (unitAn z).meromorphicAt.mul (hZ z).meromorphicAt
  have hOrder (z : ℂ) : meromorphicOrderAt G z = meromorphicOrderAt Z₀ z :=
    normPower_mul_sLocalIdelicZFunction_order χ f z r hr
  have hcovered (z : ℂ) (hz : 0 ≤ meromorphicOrderAt (rho(χ)) z) :
      0 ≤ meromorphicOrderAt Z₀ z := by
    simpa only [min_eq_left hz] using sLocalIdelicZFunction_poles f χ z
  have hRight (z : ℂ) (hz : z.re = 1) : 0 ≤ meromorphicOrderAt Z₀ z := by
    have hh := sLocalIdelicZFunction_schwartzOnStrip f χ (1/2) (3/2) (by norm_num) (by norm_num) 0
    have H : DifferentiableOn ℂ Z₀ (Complex.re ⁻¹' Ioo (1/2) (3/2)) := by
      simpa only [iteratedDeriv_zero] using hh.2.1
    exact (H.analyticAt ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      (by change 1/2 < z.re ∧ z.re < 3/2; rw [hz]; norm_num))).meromorphicOrderAt_nonneg
  have hVa : Complex.VerticalIntegrable G (-A) := normPower_mul_verticalIntegrable_of_order
    χ f r hr (-A) (neg_ne_zero.mpr hA.ne') (fun y ↦ hcovered _ (hLeft _ (by simp)))
  have hVb : Complex.VerticalIntegrable G 1 := normPower_mul_verticalIntegrable_of_order
    χ f r hr 1 one_ne_zero (fun y ↦ hRight _ (by simp))
  refine ⟨hVa, hVb, ?_⟩
  let hor (h : ℝ) := ∫ x in (-A)..1, G (vz(x,h))
  let vert (σ : ℝ) (n : ℕ) := Complex.I * ∫ y in lo n..hi n, G (vz(σ,y))
  have hvA : Tendsto (vert (-A)) atTop (𝓝 (verticalLineIntegral G (-A))) :=
    (intervalIntegral_tendsto_integral hVa hlo hhi).const_mul Complex.I
  have hvB : Tendsto (vert 1) atTop (𝓝 (verticalLineIntegral G 1)) :=
    (intervalIntegral_tendsto_integral hVb hlo hhi).const_mul Complex.I
  have hab : -A < 1 := by linarith
  have hlabs := tendsto_abs_atBot_atTop.comp hlo
  have huabs := tendsto_abs_atTop_atTop.comp hhi
  have hLo : Tendsto (fun n ↦ hor (lo n)) atTop (𝓝 0) :=
    contour_horizontal_tendsto χ η f he heq r hr hab.le lo hlabs c hc (fun n x hx ↦ (hP n x hx).1)
  have hHi : Tendsto (fun n ↦ hor (hi n)) atTop (𝓝 0) :=
    contour_horizontal_tendsto χ η f he heq r hr hab.le hi huabs c hc (fun n x hx ↦ (hP n x hx).2)
  obtain ⟨T, hReg⟩ := nonpole_on_large_euler_lines χ η f he heq (-A) 1
  have hid : ∀ᶠ n : ℕ in atTop, (hor (lo n) - hor (hi n) + vert 1 n - vert (-A) n)/I₂ =
      ∑ z ∈ sLocalStripPoleWindow χ A (lo n, hi n), complexResidue G z := by
    filter_upwards [hlabs.eventually_gt_atTop T, huabs.eventually_gt_atTop T,
      hlo.eventually_lt_atBot 0, hhi.eventually_gt_atTop 0] with n htl hth hnl hnh
    let D := sLocalStripPoleWindow χ A (lo n, hi n)
    have hD (z : ℂ) : z ∈ D ↔
        z.re ∈ Ioo (-A) 1 ∧ z.im ∈ Ioo (lo n) (hi n) ∧ meromorphicOrderAt (rho(χ)) z < 0 :=
      mem_sLocalStripPoleWindow
    have hrect := rectangleIntegral_eq_sum_complexResidue (g := G) hab (hnl.trans hnh) D
      (fun z _ ↦ hMG z) (fun z hz ↦ ⟨((hD z).mp hz).1, ((hD z).mp hz).2.1⟩) ?_
    · apply (div_eq_iff hI).mpr
      simpa only [mul_comm _ I₂] using hrect
    · rintro z ⟨⟨hr₁,hr₂⟩,⟨hi₁,hi₂⟩⟩ hn
      rw [hOrder]
      rcases hr₁.eq_or_lt with h | h₁
      · exact hcovered _ (hLeft _ h.symm)
      rcases hr₂.eq_or_lt with h | h₂
      · exact hRight _ h
      have key (y : ℝ) (hy : z.im = y) (ht : T < |y|)
          (hE : c ≤ ‖P(η,vz(z.re,y))‖) : 0 ≤ meromorphicOrderAt Z₀ z := by
        have heq' : vz(z.re,y) = z := by rw [← hy, Complex.re_add_im]
        exact hReg z ⟨h₁.le,h₂.le⟩ (hy ▸ ht) (norm_pos_iff.mp (hc.trans_le (heq' ▸ hE)))
      rcases hi₁.eq_or_lt with h | h₃
      · exact key _ h.symm htl (hP n z.re ⟨h₁.le,h₂.le⟩).1
      rcases hi₂.eq_or_lt with h | h₄
      · exact key _ h hth (hP n z.re ⟨h₁.le,h₂.le⟩).2
      exact hcovered _ (le_of_not_gt fun h ↦ hn ((hD z).mpr ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩,h⟩))
  simpa only [sub_self, zero_add] using ((((hLo.sub hHi).add hvB).sub hvA).div_const I₂).congr' hid

open Classical in
/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. At admissible cutoffs the genuine
Mellin pole sums over a common rectangle converge pointwise to the difference
of the two normalized vertical integrals, with the character conjugated. -/
theorem sLocalMellinPoleTerm_commonHeight_limit
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (rho(χ)) a) :
    ∃ lo hi : ℕ → ℝ, Tendsto lo atTop atBot ∧ Tendsto hi atTop atTop ∧
      ∀ (f : Tests) (g : Jₛ),
        let W := fun z : ℂ ↦ ((((normₛ g).val : ℝ) : ℂ)^(-z)) * Z(f,χ,z)
        Tendsto (fun n : ℕ ↦ ∑ a ∈ sLocalStripPoleWindow χ A (lo n, hi n),
          sLocalMellinPoleTerm χ f g a) atTop
          (𝓝 (star (χ g : ℂ) * ((verticalLineIntegral W 1 - verticalLineIntegral W (-A)) /
            (2 * (Real.pi : ℂ) * Complex.I)))) := by
  obtain ⟨lo, hi, hlo, hhi, hlim⟩ := sLocalIdelicZFunction_commonHeight_residue_limit χ A hA hLeft
  refine ⟨lo, hi, hlo, hhi, fun f g ↦ ?_⟩
  have hr : 0 < (((normₛ g).val : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  simpa only [sLocalMellinPoleTerm, ← Finset.mul_sum] using
    ((hlim f _ hr).2.2.const_mul (star (χ g : ℂ)))


end CommonHeightContour

section

open scoped Classical

local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "P(" η "," z ")" => ∏ v : S, (finiteHeckeEulerFactor η v.val z)⁻¹
local notation "Z(" f "," χ "," z ")" => sLocalIdelicZFunction f (chart(χ) z)
local notation "strip(" χ "," A ")" => {a : ℂ // a.re ∈ Ioo (-A) 1 ∧
  meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0}
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) normₛ (isProperMap_sIdeleQuotientNorm F S).continuous

/-- When every assigned window converges, summing its limits gives the common-height
contour difference at the given test and idèle. -/
private theorem sLocal_sum_assigned_eq_verticalLineIntegral_sub_of_tendsto {ι : Type*} [Fintype ι]
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a)
    (assign : ℂ → ι) (f : Tests) (g : Jₛ)
    (hpoint : ∀ v : ι, Tendsto (fun h ↦ ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v),
      sLocalMellinPoleTerm χ f g a) (atBot ×ˢ atTop) (𝓝 (sLocalAssignedMellinPoleSum χ A assign v f g))) :
    let W (z : ℂ) := ((((normₛ g).val : ℝ) : ℂ) ^ (-z)) * Z(f,χ,z)
    ∑ v, sLocalAssignedMellinPoleSum χ A assign v f g =
      star (χ g : ℂ) * ((verticalLineIntegral W 1 - verticalLineIntegral W (-A)) /
        (2 * (Real.pi : ℂ) * Complex.I)) := by
  obtain ⟨lo, hi, hlo, hhi, hcontour⟩ := sLocalMellinPoleTerm_commonHeight_limit χ A hA hLeft
  have htot := tendsto_finsetSum Finset.univ (fun v _ ↦ (hpoint v).comp (hlo.prodMk hhi))
  exact tendsto_nhds_unique (htot.congr (fun n ↦ Finset.sum_fiberwise
    (sLocalStripPoleWindow χ A (lo n, hi n)) assign (sLocalMellinPoleTerm χ f g))) (hcontour f g)

/-- Paper: Theorem 7.1.2.3, p. 322. At a pole-free left boundary, the sum over any finite
assignment of one-prime poles equals the normalized contour difference for the actual
Mellin chart. Each assigned sum is its unconditional sum in the open strip. -/
theorem sLocalSinglePrime_sum_assigned_eq_verticalLineIntegral_sub {ι : Type*} [Fintype ι]
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a)
    (assign : ℂ → ι) (f : Tests) (g : Jₛ) :
    let W (z : ℂ) := ((((normₛ g).val : ℝ) : ℂ) ^ (-z)) * Z(f,χ,z)
    ∑ v, sLocalAssignedMellinPoleSum χ A assign v f g =
      star (χ g : ℂ) * ((verticalLineIntegral W 1 - verticalLineIntegral W (-A)) /
        (2 * (Real.pi : ℂ) * Complex.I)) := by
  apply sLocal_sum_assigned_eq_verticalLineIntegral_sub_of_tendsto χ A hA hLeft assign f g
  intro v
  have hu := ((sLocalSinglePrime_separatePlace_absolute χ A hsame assign).2 v
    {f} (Bornology.isVonNBounded_singleton _) {g} isCompact_singleton).1
  exact hu.tendsto_at (x := (f, g)) ⟨mem_singleton _, mem_singleton _⟩

section BoundedVerticalLine

local notation "vz(" σ "," y ")" => ((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I
local notation "rho(" χ ")" => (fun z : ℂ ↦ sLocalRhoFactor (chart(χ) z))

private theorem sLocalIdelicZFunction_weighted_regular_line
    (χ : PontryaginDual Jₛ) (σ : ℝ) (hσ : σ ≠ 0)
    (hreg : ∀ y : ℝ, 0 ≤ meromorphicOrderAt (rho(χ)) (vz(σ,y))) (f : Tests) :
    ∃ C : ℝ, ∀ y : ℝ, (1 + y^2) * ‖Z(f,χ,vz(σ,y))‖ ≤ C := by
  obtain ⟨η, hη, he, -⟩ := sLocal_character_extension χ
  obtain ⟨C, _, T, htail⟩ := sLocalIdelicZFunction_cleared_strip_tails χ η f hη he σ σ 2
  obtain ⟨c, hc, hP⟩ := euler_reciprocal_lower_on_line (S := S) η σ hσ
  let M := max T 1
  let W (y : ℝ) := (1 + y^2) * ‖Z(f,χ,vz(σ,y))‖
  have hZ (y : ℝ) := ((sLocalIdelicZFunction_meromorphic f χ) (mem_univ (vz(σ,y)))).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((le_min le_rfl (hreg y)).trans (sLocalIdelicZFunction_poles f χ _))
  have hW : Continuous W := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (continuous_const.add (continuous_id.pow 2)).continuousAt.mul
      ((ContinuousAt.comp (f := fun x : ℝ ↦ vz(σ,x)) (g := fun z ↦ Z(f,χ,z))
        (hZ y).continuousAt (by fun_prop)).norm)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-M) M) (f := W) hW.continuousOn
  refine ⟨max D (2*(C/c)), fun y ↦ ?_⟩
  by_cases hy : |y| ≤ M
  · exact ((le_abs_self (W y)).trans (hD y (abs_le.mp hy))).trans (le_max_left _ _)
  have hyM := lt_of_not_ge hy
  have hyT := (le_max_left T 1).trans_lt hyM
  have hy1 : 1 ≤ |y| := ((le_max_right T 1).trans_lt hyM).le
  have hb := htail (vz(σ,y)) (by simp) (by simpa using hyT)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add, sq_abs, norm_mul] at hb
  have hsize : y^2 * ‖Z(f,χ,vz(σ,y))‖ ≤ C/c := by
    apply (le_div_iff₀ hc).mpr
    calc
      _ ≤ y^2 * ‖Z(f,χ,vz(σ,y))‖ * ‖P(η,vz(σ,y))‖ :=
        mul_le_mul_of_nonneg_left (hP y) (by positivity)
      _ = _ := by ring
      _ ≤ _ := hb
  have hy2 : 1 ≤ y^2 := by rw [← sq_abs]; exact one_le_pow₀ hy1
  apply (le_max_right _ _).trans'
  calc
    (1 + y^2) * _ ≤ (2 * y^2) * ‖Z(f,χ,vz(σ,y))‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ = 2 * (y^2 * ‖Z(f,χ,vz(σ,y))‖) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hsize (by norm_num)

/-- Paper: Theorem 7.1.2.3, pp. 322–323. On any pole-free vertical line of
nonzero real part, the L¹ norms of the actual zeta integrals are bounded
uniformly on each von Neumann bounded set of test functions. -/
theorem sLocalIdelicZFunction_vertical_L1_bounded
    (χ : PontryaginDual Jₛ) (σ : ℝ) (hσ : σ ≠ 0)
    (hreg : ∀ y : ℝ, 0 ≤ meromorphicOrderAt (rho(χ)) (vz(σ,y)))
    (B : Set Tests) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C ≥ (0 : ℝ), ∀ f ∈ B, (∫ y : ℝ, ‖Z(f,χ,vz(σ,y))‖) ≤ C := by
  classical
  let : BarrelledSpace ℂ Tests := (sAdeleSchwartz_montel (F := F) S).1
  have horder (y : ℝ) : 0 ≤ sLocalIdelicOrderBound (chart(χ) (vz(σ,y))) := by
    let t := vz(σ,y)
    have hshift := unitaryChart_normTwist_add χ t
    change 0 ≤ min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor
      (quasiCharacterNormTwist normₛ (isProperMap_sIdeleQuotientNorm F S).continuous
        (chart(χ) t) z)) 0)
    simp only [hshift]
    change 0 ≤ min 0 (meromorphicOrderAt (fun z ↦ (rho(χ)) (z + t)) 0)
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := rho(χ)) (c := t) (x := (0 : ℂ)), zero_add]
    exact le_min le_rfl (hreg y)
  let E (y : ℝ) : StrongDual ℂ Tests := ((1+y^2 : ℝ) : ℂ) •
    ((ContinuousMap.evalCLM ℂ ⟨chart(χ) (vz(σ,y)), horder y⟩).comp
      ((Submodule.subtypeL _).comp ⟨sLocalIdelicMellin,sLocalIdelicMellin_continuous⟩))
  have hE (y : ℝ) (f : Tests) : ‖E y f‖ = (1+y^2) * ‖Z(f,χ,vz(σ,y))‖ := by
    change ‖((1+y^2 : ℝ) : ℂ) * Z(f,χ,vz(σ,y))‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb (f : Tests) : ∃ C : ℝ, ∀ y : ℝ, ‖E y f‖ ≤ C := by
    simpa only [hE] using sLocalIdelicZFunction_weighted_regular_line χ σ hσ hreg f
  obtain ⟨C, hC⟩ := strongDual_family_bounded_on_bounded_set E hb hB
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D * Real.pi, mul_nonneg hD Real.pi_pos.le, fun f hf ↦ ?_⟩
  have hline := normPower_mul_verticalIntegrable_of_order χ f 1 one_pos σ hσ
    (fun y ↦ (le_min le_rfl (hreg y)).trans (sLocalIdelicZFunction_poles f χ _))
  have hZ : Integrable (fun y : ℝ ↦ ‖Z(f,χ,vz(σ,y))‖) := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_one, Complex.one_cpow, one_mul] using hline.norm
  calc
    (∫ y : ℝ, ‖Z(f,χ,vz(σ,y))‖) ≤ ∫ y : ℝ, D * (1 + y^2)⁻¹ := by
      apply integral_mono hZ (integrable_inv_one_add_sq.const_mul D)
      intro y
      change ‖Z(f,χ,vz(σ,y))‖ ≤ D * (1+y^2)⁻¹
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (by positivity : 0 < 1 + y^2)).mpr
      rw [mul_comm, ← hE]
      exact (hC y f hf).trans (le_max_left _ _)
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- The left vertical integral has the exact norm weight of the repaired theta
remainder. The coefficient is finite on every admissible line. -/
private theorem norm_verticalLineIntegral_normPower_mul_le
    (Z : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (A : ℝ) :
    ‖verticalLineIntegral (fun z ↦ (r : ℂ)^(-z) * Z z) (-A) / (2 * (Real.pi : ℂ) * Complex.I)‖ ≤
      ((∫ y : ℝ, ‖Z (vz(-A,y))‖) / (2 * Real.pi)) * r ^ A := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hpC : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_div, hpC, verticalLineIntegral, norm_mul, Complex.norm_I, one_mul]
  calc
    _ ≤ (∫ y : ℝ, ‖(r : ℂ)^(-(vz(-A,y))) * Z (vz(-A,y))‖) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) hp.le
    _ = _ := by
      have he (y : ℝ) : ‖(r : ℂ)^(-(vz(-A,y))) * Z (vz(-A,y))‖ =
          r ^ A * ‖Z (vz(-A,y))‖ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr]
        simp
      simp only [he, integral_const_mul]
      ring

/-- The normalized left-line remainder is uniformly O(rᴬ) on every bounded
set of test functions, with a constant independent of the positive norm r. -/
theorem sLocalIdelicZFunction_leftIntegral_bounded_remainder
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (rho(χ)) a)
    (B : Set Tests) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C ≥ (0 : ℝ), ∀ f ∈ B, ∀ r : ℝ, 0 < r →
      ‖verticalLineIntegral (fun z ↦ (r : ℂ)^(-z) * Z(f,χ,z)) (-A) /
        (2 * (Real.pi : ℂ) * Complex.I)‖ ≤ C * r^A := by
  obtain ⟨D, hD, hb⟩ := sLocalIdelicZFunction_vertical_L1_bounded χ (-A)
    (neg_ne_zero.mpr hA.ne') (fun y ↦ hLeft _ (by simp)) B hB
  refine ⟨D/(2*Real.pi), by positivity, fun f hf r hr ↦ ?_⟩
  apply (norm_verticalLineIntegral_normPower_mul_le (fun z ↦ Z(f,χ,z)) r hr A).trans
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hb f hf) (by positivity))
    (Real.rpow_nonneg hr.le _)

end BoundedVerticalLine

section ThetaInversion

/-- The normalized, upward-oriented vertical integral has Mathlib's inverse Mellin
normalization. -/
private theorem normalizedVerticalLineIntegral_normPower_eq_mellinInv (Z : ℂ → ℂ) (σ r : ℝ) :
    verticalLineIntegral (fun z ↦ (r : ℂ) ^ (-z) * Z z) σ /
      (2 * (Real.pi : ℂ) * Complex.I) = mellinInv σ Z r := by
  unfold verticalLineIntegral mellinInv
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero]

/-- Mellin inversion for the specific positive-real Haar measure used in the S-local norm
decomposition. The logarithmic change of variables fixes its normalization. -/
private theorem mellinInv_positiveRealHaar {H : ℝ≥0ˣ → ℂ} (hH : Continuous H)
    (Z : ℂ → ℂ) (σ : ℝ) (u : ℝ≥0ˣ)
    (hM : ∀ s : ℂ, s.re = σ → Z s =
      ∫ t : ℝ≥0ˣ, H t * ((((t : ℝ≥0) : ℝ) : ℂ) ^ s) ∂positiveRealHaar)
    (hI : Integrable (fun t : ℝ≥0ˣ ↦ H t * ((((t : ℝ≥0) : ℝ) : ℂ) ^ (σ : ℂ))) positiveRealHaar)
    (hV : Complex.VerticalIntegrable Z σ) : mellinInv σ Z (u.val : ℝ) = H u := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let f (t : ℝ) := H (e (Real.log t))
  have hmeasure : positiveRealHaar = volume.map e := by
    apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
    funext x
    exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos x).le))
  have hp (x : ℝ) (s : ℂ) : ((((e x : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s = Complex.exp (s * x) := by
    change (Real.exp x : ℂ) ^ s = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]
  have htrans (s : ℂ) :
      mellin f s = ∫ t : ℝ≥0ˣ, H t * ((((t : ℝ≥0) : ℝ) : ℂ) ^ s) ∂positiveRealHaar := by
    rw [hmeasure, e.measurableEmbedding.integral_map, mellin, ← integral_comp_exp]
    apply integral_congr_ae
    filter_upwards with x
    simp only [f, Real.log_exp, Complex.real_smul, smul_eq_mul, hp]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
    simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    rw [mul_comm (H (e x))]
    congr 2
    ring
  have hconv : MellinConvergent f (σ : ℂ) := by
    apply mellinConvergent_of_integrable_logWeight (fun x ↦ H (e x))
    rw [hmeasure] at hI
    apply (e.measurableEmbedding.integrable_map_iff.mp hI).congr
    filter_upwards with x
    change H (e x) * _ = _
    rw [hp, mul_comm (H (e x))]
    simp
  have hz (y : ℝ) : Z ((σ : ℂ) + y * Complex.I) = mellin f ((σ : ℂ) + y * Complex.I) :=
    (hM _ (by simp)).trans (htrans _).symm
  have hv : Complex.VerticalIntegrable (mellin f) σ := hV.congr (.of_forall hz)
  have hu : 0 < (u.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt u)
  have hf : ContinuousAt f (u.val : ℝ) :=
    hH.continuousAt.comp (e.continuous.continuousAt.comp (Real.continuousAt_log hu.ne'))
  have he : e (Real.log (u.val : ℝ)) = u := Units.ext (NNReal.eq (Real.exp_log hu))
  calc
    mellinInv σ Z (u.val : ℝ) = mellinInv σ (mellin f) (u.val : ℝ) := by
      simp only [mellinInv, hz]
    _ = f (u.val : ℝ) := mellinInv_mellin_eq _ _ hu hconv hv hf
    _ = H u := congrArg H he

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "J₁" => (normₛ).ker
local notation "μ" => sLocalNormOneQuotientMeasure F S

local notation "ω(" χ ")" => (χ : PontryaginDual Jₛ).comp
  (⟨(normₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)

/-- On every positive line, inverse Mellin of the actual S-local zeta function recovers
the genuine homogeneous theta multiplied by the unitary character. -/
private theorem sLocal_mellinInv_eq_character_mul_theta (χ : PontryaginDual Jₛ) (f : Tests)
    (g : Jₛ) {σ : ℝ} (hσ : 0 < σ) :
    mellinInv σ (fun z ↦ sLocalIdelicZFunction f (chart(χ) z)) ((normₛ g).val : ℝ) =
      (χ g : ℂ) * sLocalHomogeneousAdelicTheta F S μ (ω(χ)) f g := by
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Iₛ := ⟨p.comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := sIdeleNorm_project_canonicalSection F S
  let q : ℝ≥0ˣ →ₜ* Jₛ := (⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩ : Iₛ →ₜ* Jₛ).comp τ
  have hq (t : ℝ≥0ˣ) : normₛ (q t) = t := hτ t
  let θ := sLocalHomogeneousAdelicTheta F S μ (ω(χ)) f
  let H (t : ℝ≥0ˣ) := (χ (q t) : ℂ) * θ (q t)
  let R (t : ℝ≥0ˣ) : ℂ := (((t.val : ℝ≥0) : ℝ) : ℂ)
  let Z (z : ℂ) := sLocalIdelicZFunction f (chart(χ) z)
  have hH : Continuous H :=
    (continuous_subtype_val.comp (χ.continuous.comp q.continuous)).mul (θ.continuous.comp q.continuous)
  have hraw (s : ℂ) : (fun t : ℝ≥0ˣ ↦ θ (q t) * chart(χ) s (q t)) =
      (fun t : ℝ≥0ˣ ↦ H t * R t ^ s) := by
    funext t
    change θ (q t) * ((χ (q t) : ℂ) * R (normₛ (q t)) ^ s) = ((χ (q t) : ℂ) * θ (q t)) * R t ^ s
    rw [hq]
    ring
  have hM (s : ℂ) (hs : s.re = σ) :
      Z s = ∫ t : ℝ≥0ˣ, H t * R t ^ s ∂positiveRealHaar := by
    have hs' : 0 < s.re := hs ▸ hσ
    have hc : ∃ (η : PontryaginDual Jₛ) (w : ℂ), 0 < w.re ∧ chart(χ) s = chart(η) w :=
      ⟨χ, s, hs', rfl⟩
    change sLocalIdelicZFunction f (chart(χ) s) = _
    rw [sLocalIdelicZFunction_eq_integral f hc, ← sLocalThetaMellinIntegral_eq_zeta f hc,
      ← sLocalRadialMellinIntegral_eq_theta τ hτ f χ s hs']
    change (∫ t : ℝ≥0ˣ, θ (q t) * chart(χ) s (q t) ∂positiveRealHaar) = _
    rw [hraw]
  have hI : Integrable (fun t : ℝ≥0ˣ ↦ H t * R t ^ (σ : ℂ)) positiveRealHaar := by
    rw [← hraw]
    exact sLocalRadialMellinIntegral_integrable τ hτ f χ (σ : ℂ) hσ
  have hs := sLocalIdelicZFunction_schwartzOnStrip f χ (σ / 2) (σ + 1) (half_pos hσ) (by linarith) 0
  have hV : Complex.VerticalIntegrable Z σ :=
    (show UniformlySchwartzOnStrip Z (σ / 2) (σ + 1) by simpa only [iteratedDeriv_zero] using hs).verticalIntegrable
      σ ⟨by linarith, by linarith⟩
  have hi := mellinInv_positiveRealHaar hH Z σ (normₛ g) hM hI hV
  change mellinInv σ Z ((normₛ g).val : ℝ) = (χ g : ℂ) * θ g
  rw [hi]
  let k : J₁ := ⟨g / q (normₛ g), by rw [MonoidHom.mem_ker, map_div, hq, div_self']⟩
  have hk : k.val⁻¹ * g = q (normₛ g) := (inv_mul_eq_iff_eq_mul).mpr (div_mul_cancel _ _).symm
  have hθ := sLocalHomogeneousAdelicTheta_homogeneous F S μ (ω(χ)) f k g
  change θ (k.val⁻¹ * g) = (χ k.val : ℂ) * θ g at hθ
  change (χ (q (normₛ g)) : ℂ) * θ (q (normₛ g)) = _
  rw [hk] at hθ
  rw [hθ, ← mul_assoc, ← Circle.coe_mul, ← map_mul]
  congr 3
  change q (normₛ g) * (g / q (normₛ g)) = g
  rw [mul_comm (q (normₛ g)) (g / q (normₛ g)), div_mul_cancel]

/-- The packaged theta is the conjugate-character multiple of the normalized right
vertical integral, with no choice of section or measure left in the statement. -/
theorem sLocal_theta_eq_normalized_right_line (χ : PontryaginDual Jₛ) (f : Tests) (g : Jₛ)
    {σ : ℝ} (hσ : 0 < σ) :
    sLocalHomogeneousAdelicTheta F S μ (ω(χ)) f g =
      star (χ g : ℂ) * (verticalLineIntegral (fun z ↦
        ((((normₛ g).val : ℝ) : ℂ) ^ (-z)) * sLocalIdelicZFunction f (chart(χ) z)) σ /
          (2 * (Real.pi : ℂ) * Complex.I)) := by
  have hi : star (χ g : ℂ) = ((χ g)⁻¹ : Circle) := (Circle.coe_inv_eq_conj _).symm
  rw [normalizedVerticalLineIntegral_normPower_eq_mellinInv, sLocal_mellinInv_eq_character_mul_theta χ f g hσ,
    ← mul_assoc, hi, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]

/-- Subtracting the value of the shifted contour from the genuine theta leaves exactly
the norm of the normalized left line. -/
private theorem norm_sLocalTheta_sub_normalizedContour_eq_left (χ : PontryaginDual Jₛ) (f : Tests)
    (g : Jₛ) (A : ℝ) :
    let W (z : ℂ) := ((((normₛ g).val : ℝ) : ℂ) ^ (-z)) * sLocalIdelicZFunction f (chart(χ) z)
    ‖sLocalHomogeneousAdelicTheta F S μ (ω(χ)) f g -
      star (χ g : ℂ) * ((verticalLineIntegral W 1 - verticalLineIntegral W (-A)) /
        (2 * (Real.pi : ℂ) * Complex.I))‖ =
      ‖verticalLineIntegral W (-A) / (2 * (Real.pi : ℂ) * Complex.I)‖ := by
  intro W
  rw [sLocal_theta_eq_normalized_right_line χ f g (σ := 1) zero_lt_one]
  change ‖star (χ g : ℂ) * (verticalLineIntegral W 1 / _) -
    star (χ g : ℂ) * ((verticalLineIntegral W 1 - verticalLineIntegral W (-A)) / _)‖ = _
  have he : verticalLineIntegral W 1 - (verticalLineIntegral W 1 - verticalLineIntegral W (-A)) =
      verticalLineIntegral W (-A) := by ring
  rw [← mul_sub, ← sub_div, he, norm_mul, norm_star, Circle.norm_coe, one_mul]

end ThetaInversion

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323, and (8.4.0.1)–(8.4.0.3), p. 389. At a
regular left boundary, inverse-square residue bounds on compact idèle sets for each test
imply the separate-place theta expansion for every assignment. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_residue_decay
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hdecay : ∀ (f : Tests) (K : Set Jₛ), IsCompact K →
      ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| → ∀ g ∈ K,
        ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|) ^ 2)
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a)
    (assign : ℂ → Places) : sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign := by
  have hlimits := (sLocalMellinPoleTerm_separatePlace_absolute_of_residue_decay χ A hdecay assign).2
  have hcontour (f : Tests) (g : Jₛ) :=
    sLocal_sum_assigned_eq_verticalLineIntegral_sub_of_tendsto χ A hA hLeft assign f g (fun v ↦
      ((hlimits v {f} (Bornology.isVonNBounded_singleton _) {g} isCompact_singleton).1).tendsto_at
        (x := (f, g)) ⟨mem_singleton _, mem_singleton _⟩)
  obtain ⟨_, _, _, _, hvertical⟩ := sLocalIdelicZFunction_commonHeight_residue_limit χ A hA hLeft
  refine ⟨fun v f g ↦ sLocalAssignedMellinPoleSum χ A assign v f g, ?_, ?_, ?_, ?_⟩
  · intro v f K hK
    have hu := (hlimits v {f} (Bornology.isVonNBounded_singleton _) K hK).1
    have hK' := (hu.comp (fun g ↦ (f, g))).mono (s' := K) (fun g hg ↦ ⟨mem_singleton _, hg⟩)
    apply hK'.congr
    filter_upwards with h g _
    apply Finset.sum_congr ?_ (fun _ _ ↦ rfl)
    ext a
    simp only [Finset.mem_filter, sLocalStripPoleWindow]
  · intro v g _ B hB
    have hu := (hlimits v B hB {g} isCompact_singleton).1
    have hB' := (hu.comp (fun f ↦ (f, g))).mono (s' := B) (fun f hf ↦ ⟨hf, mem_singleton _⟩)
    apply hB'.congr
    filter_upwards with h f _
    apply Finset.sum_congr ?_ (fun _ _ ↦ rfl)
    ext a
    simp only [Finset.mem_filter, sLocalStripPoleWindow]
  · intro f
    refine ⟨?_, fun g _ ↦ ?_⟩
    · simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using (hvertical f 1 zero_lt_one).1
    · rw [hcontour f g,
        norm_sLocalTheta_sub_normalizedContour_eq_left]
      exact norm_verticalLineIntegral_normPower_mul_le (fun z ↦ Z(f,χ,z)) _ (NNReal.coe_pos.mpr (Units.zero_lt _)) A
  · intro B hB
    obtain ⟨C, hC, hb⟩ := sLocalIdelicZFunction_leftIntegral_bounded_remainder χ A hA hLeft B hB
    refine ⟨C, hC, fun f hf g _ ↦ ?_⟩
    rw [hcontour f g,
      norm_sLocalTheta_sub_normalizedContour_eq_left]
    exact hb f hf _ (NNReal.coe_pos.mpr (Units.zero_lt _))

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323, and (8.4.0.1)–(8.4.0.3), p. 389. When the
finite places lie over one rational prime and the left boundary is free of correcting-factor
poles, the repaired separate-place theta expansion holds for every assignment. In particular,
a shared pole can be assigned to any one of its contributing places. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_same_prime
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a)
    (assign : ℂ → Places) : sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign :=
  sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_residue_decay χ A hA
    (fun f K hK ↦ sLocalStripPoles_weighted_residue_decay_of_same_prime χ A hsame f K hK 2) hLeft assign

/-- Every one-prime datum at an admissible cutoff has a valid assignment realizing the
full separate-place expansion of Theorem 7.1.2.3. -/
theorem exists_sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_same_prime
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ))
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a) :
    ∃ assign : ℂ → Places, IsValidPoleAssignment χ assign ∧
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign := by
  obtain ⟨assign, hvalid⟩ := exists_isValidPoleAssignment χ
  exact ⟨assign, hvalid, sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_same_prime
    χ A hA hsame hLeft assign⟩

/-- Every positive cutoff has a right neighborhood of admissible cutoffs. Equivalently the
left contour can move a little farther left, with only possible boundary poles at the
original abscissa. -/
theorem eventually_sLocal_leftBoundary_regular (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ B : ℝ in 𝓝[>] A, ∀ a : ℂ, a.re = -B →
      0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a := by
  let E := {a : ℂ | a.re ∈ Icc (-(A + 1)) 1 ∧
    ∃ w : InfinitePlace F, sLocalPoleContributes χ (.inl w) a}
  have hfin : E.Finite := sLocalPoleContributes_archimedean_finite_in_strip χ (A + 1)
  let bad := ((fun a : ℂ ↦ -a.re) '' E) \ {A}
  have hbad : bad.Finite := (hfin.image _).sdiff
  have hnb : badᶜ ∈ 𝓝 A := hbad.isClosed.isOpen_compl.mem_nhds
    (show A ∈ badᶜ from fun h ↦ h.2 (mem_singleton A))
  filter_upwards [Ioo_mem_nhdsGT (show A < A + 1 by linarith),
    mem_nhdsWithin_of_mem_nhds hnb] with B hB hb a ha
  by_contra hn
  obtain ⟨w | v, hv⟩ := (sLocalPoleContributes_exists_iff χ a).mp (lt_of_not_ge hn)
  · have haE : a ∈ E := ⟨by rw [ha]; constructor <;> linarith [hB.1, hB.2], w, hv⟩
    exact hb ⟨⟨a, haE, by change -a.re = B; rw [ha, neg_neg]⟩, fun h ↦ hB.1.ne' (mem_singleton_iff.mp h)⟩
  · obtain ⟨m, t, _, _, he⟩ := hv
    rw [he, Complex.mul_I_re, Complex.ofReal_im, neg_zero] at ha
    linarith [hB.1]

/-- For any requested positive cutoff, every sufficiently small shift of the left contour
farther left gives a cutoff at which the full one-prime separate-place expansion holds. -/
theorem eventually_sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_same_prime
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    ∀ᶠ B : ℝ in 𝓝[>] A, ∃ hB : 0 < B, ∀ assign : ℂ → Places,
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ B hB assign := by
  filter_upwards [eventually_sLocal_leftBoundary_regular χ A hA, self_mem_nhdsWithin] with B hreg hB
  have hpos : 0 < B := hA.trans hB
  exact ⟨hpos, sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_same_prime χ B hpos hsame hreg⟩

/-! ## Separate residues under polynomial separation of the finite poles -/

/-- The norm power in the global finite Euler denominator has real logarithm
and negative exponent in the additive spectral coordinate. -/
private theorem finitePlace_absNorm_cpow_neg_eq_exp (v : HeightOneSpectrum (𝓞 F)) (z : ℂ) :
    (v.asIdeal.absNorm : ℂ) ^ (-z) =
      Complex.exp (-((Real.log (v.asIdeal.absNorm : ℝ)) : ℂ) * z) := by
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt (HeightOneSpectrum.one_lt_absNorm v)
  rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    ← Complex.ofReal_log hq.le, mul_neg, neg_mul]

/-- At a place of S where the global extension is unramified, its local Euler
denominator vanishes precisely at the poles contributed by the stage character. -/
theorem sLocalPoleContributes_finite_iff_globalEulerRoot (χ : PontryaginDual Jₛ) (η : U)
    (h : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist η 0, h⟩ = chart(χ) 0)
    (v : S) (hvr : (ideleClassNormTwist η 0).IsUnramifiedAt v.val) (b : ℂ) :
    sLocalPoleContributes χ (Sum.inr v) b ↔
      (ideleClassNormTwist η 0).localValue v.val *
        Complex.exp (-((Real.log (v.val.asIdeal.absNorm : ℝ)) : ℂ) * b) = 1 := by
  let ψ := sLocalFiniteRestriction v (chart(χ) 0)
  have hψ (x : (v.val.adicCompletion F)ˣ) : ‖ψ x‖ = 1 := by
    change ‖((χ _ : Circle) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  have hres (x : (v.val.adicCompletion F)ˣ) : ψ x = (ideleClassNormTwist η 0).restrict v.val x.val := by
    change sLocalFiniteRestriction v (chart(χ) 0) x = _
    rw [← he, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    exact sLocalFiniteRestriction_sIdeleRestriction _ v x
  have hU (u : (v.val.adicCompletionIntegers F)ˣ) :
      ψ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 :=
    (hres _).trans (hvr.restrict_apply_unit_eq_one u)
  let val : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π₀, hπ₀⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 (π₀ : v.val.adicCompletion F) hπ₀.ne_zero
  have hπ : ‖π.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v.val π.val hπ₀
  have hvalue : ψ π = (ideleClassNormTwist η 0).localValue v.val :=
    (hres π).trans (hvr.localValue_eq π.val hπ₀).symm
  have hpow : ((‖π.val‖ : ℝ) : ℂ) ^ b =
      Complex.exp (-((Real.log (v.val.asIdeal.absNorm : ℝ)) : ℂ) * b) := by
    rw [← finitePlace_absNorm_cpow_neg_eq_exp, hπ, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) b, Complex.cpow_neg, Complex.ofReal_natCast]
  refine (sLocalRhoFactor_poles_iff_finite_explicit v.val ψ hψ π hπ b).symm.trans ?_
  rw [and_iff_right hU, hvalue, hpow]

/-- Above the archimedean pole heights, inverse-polynomial separation gives punctured
disks containing no other pole. Every point of the boundary is at least the disk radius
from every finite pole, including the center itself. -/
private theorem sLocalStripPoles_polynomial_isolating_circles
    (χ : PontryaginDual Jₛ) (A : ℝ) (hsep : sLocalFinitePolePolynomialSeparation χ) :
    ∃ d : ℕ, ∃ c > (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| →
      let r := c / (1 + |a.val.im|) ^ d
      0 < r ∧ r < 1 ∧ a.val.re = 0 ∧
        (∀ z ∈ Metric.closedBall a.val r, z ≠ a.val →
          0 ≤ meromorphicOrderAt (fun w ↦ sLocalRhoFactor (chart(χ) w)) z) ∧
        ∀ z ∈ Metric.sphere a.val r, ∀ b : ℂ,
          (∃ v : S, sLocalPoleContributes χ (Sum.inr v) b) → r ≤ ‖z - b‖ := by
  obtain ⟨k, hk, d, hgap⟩ := hsep
  obtain ⟨H, hH⟩ := sLocalStripPoles_high_finite_place χ A
  obtain ⟨Q, hQ⟩ := sLocalStripPoles_high_finite_place χ 2
  let c := min k 1 / 3
  have hc : 0 < c := div_pos (lt_min hk one_pos) (by norm_num)
  have hc₁ : c < 1 := by dsimp [c]; linarith [min_le_right k 1]
  have hc₂ : 2 * c ≤ k := by dsimp [c]; linarith [min_le_left k 1]
  refine ⟨d, c, hc, max H (Q+1), fun a ha ↦ ?_⟩
  let h := (1 + |a.val.im|) ^ d
  let r := c / h
  have hh : 1 ≤ h := one_le_pow₀ (by linarith [abs_nonneg a.val.im])
  have hhp : 0 < h := zero_lt_one.trans_le hh
  have hr : 0 < r := div_pos hc hhp
  have hr₁ : r < 1 := (div_le_self hc.le hh).trans_lt hc₁
  have hfin := hH a ((le_max_left _ _).trans_lt ha)
  obtain ⟨v, hv⟩ := hfin
  have ha₀ : a.val.re = 0 := by
    obtain ⟨m, t, _, _, he⟩ := hv
    rw [he, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  have hdist (b : ℂ) (hb : ∃ w : S, sLocalPoleContributes χ (Sum.inr w) b)
      (hne : b ≠ a.val) : 2 * r ≤ ‖b - a.val‖ := by
    calc
      2 * r = (2*c)/h := (mul_div_assoc _ _ _).symm
      _ ≤ k/h := div_le_div_of_nonneg_right hc₂ hhp.le
      _ ≤ _ := hgap _ _ ⟨v, hv⟩ hb hne.symm
  refine ⟨hr, hr₁, ha₀, fun z hz hza ↦ ?_, fun z hz b hb ↦ ?_⟩
  · have hd : ‖z-a.val‖ ≤ r := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hz
    have hre : |z.re| ≤ r := by simpa [Complex.sub_re, ha₀] using (Complex.abs_re_le_norm (z-a.val)).trans hd
    have hzi : Q < |z.im| := by
      have hδ : |a.val.im| ≤ |z.im| + r := by
        calc
          |a.val.im| = |(a.val - z).im + z.im| := by rw [Complex.sub_im, sub_add_cancel]
          _ ≤ |(a.val-z).im| + |z.im| := abs_add_le _ _
          _ ≤ _ := by linarith [Complex.abs_im_le_norm (a.val-z), norm_sub_rev a.val z]
      have hQ' : Q + 1 < |a.val.im| := (le_max_right _ _).trans_lt ha
      linarith
    apply le_of_not_gt
    intro hp
    let p : strip(χ,2) := ⟨z, ⟨by linarith [(abs_le.mp hre).1], by linarith [(abs_le.mp hre).2]⟩, hp⟩
    have := hdist z (hQ p hzi) hza
    linarith
  · have hd : ‖z-a.val‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    by_cases hb' : b = a.val
    · subst b
      exact hd.ge
    · have htri : ‖b - a.val‖ ≤ ‖z-b‖ + r := by
        rw [← hd, norm_sub_rev z b]
        simpa only [dist_eq_norm] using dist_triangle b z a.val
      linarith [hdist b hb hb']

/-- If every finite pole is at least distance r from z, the product that clears the
Euler factors is bounded below by a constant times r to the number of places. -/
private theorem reciprocal_euler_product_lower_of_separated (χ : PontryaginDual Jₛ) (η : U)
    (he : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (heq : sIdeleRestriction F S ⟨ideleClassNormTwist η 0, he⟩ = chart(χ) 0) :
    ∃ k > (0 : ℝ), ∀ (z : ℂ) (r : ℝ), 0 < r → r ≤ 1 →
      (∀ b : ℂ, (∃ v : S, sLocalPoleContributes χ (Sum.inr v) b) → r ≤ ‖z-b‖) →
      k * r^(Fintype.card S) ≤ ‖P(η,z)‖ := by
  classical
  have hL (v : S) : 0 < Real.log (v.val.asIdeal.absNorm : ℝ) :=
    Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)
  choose k hk hc using fun v : S ↦ exists_mul_le_norm_one_sub_mul_exp_of_separated _ (hL v)
  let m (v : S) := min (k v) 1
  have hm (v : S) : 0 < m v := lt_min (hk v) one_pos
  refine ⟨∏ v, m v, Finset.prod_pos (fun v _ ↦ hm v), fun z r hr hr₁ hdist ↦ ?_⟩
  have hprod : (∏ v : S, m v * r) = (∏ v : S, m v) * r ^ Fintype.card S := by
    simp [Finset.prod_mul_distrib]
  rw [← hprod, norm_prod]
  apply Finset.prod_le_prod₀ (fun v _ ↦ mul_nonneg (hm v).le hr.le)
  intro v _
  unfold finiteHeckeEulerFactor
  split_ifs with hu
  · rw [inv_inv, finitePlace_absNorm_cpow_neg_eq_exp]
    refine (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le).trans ?_
    apply hc v _ z r hr hr₁
    intro b hb
    exact hdist b ⟨v, (sLocalPoleContributes_finite_iff_globalEulerRoot χ η he heq v hu b).mpr hb⟩
  · simp only [inv_one, norm_one]
    exact (mul_le_of_le_one_right (hm v).le hr₁).trans (min_le_right _ _)

/-- Absorb the inverse power of a shrinking radius into the prescribed order of
vertical decay. Here the radius is c/h^d and h is at most twice the vertical height. -/
private theorem absorb_euler_circle_loss {h t c k p v L : ℝ} (N d n : ℕ)
    (hh : 0 < h) (ht : 0 ≤ t) (hc : 0 < c) (hk : 0 < k) (hv : 0 ≤ v)
    (hh₂ : h ≤ 2*t) (hp : k * (c/h^d)^n ≤ p)
    (hclear : t^(N+d*n) * (p*v) ≤ L) :
    v * h^N ≤ (2:ℝ)^(N+d*n)*L/(k*c^n) := by
  apply (le_div_iff₀ (mul_pos hk (pow_pos hc n))).mpr
  have hsplit : k*c^n = (k*(c/h^d)^n) * h^(d*n) := by
    rw [div_pow, pow_mul]
    field_simp [hh.ne']
  have hraise : h^(N+d*n) ≤ (2:ℝ)^(N+d*n) * t^(N+d*n) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hh.le hh₂ _
  calc
    v * h^N * (k*c^n) = h^(N+d*n) * (k*(c/h^d)^n) * v := by rw [hsplit, pow_add]; ring
    _ ≤ ((2:ℝ)^(N+d*n)*t^(N+d*n)) * p * v := mul_le_mul_of_nonneg_right
      (mul_le_mul hraise hp (mul_nonneg hk.le (pow_nonneg (div_nonneg hc.le (pow_nonneg hh.le _)) _))
        (mul_nonneg (by positivity) (pow_nonneg ht _))) hv
    _ = (2:ℝ)^(N+d*n) * (t^(N+d*n) * (p*v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hclear (by positivity)

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. On shrinking circles around all sufficiently
high poles, the weighted Mellin transform decays to every order, uniformly for idèles in
a fixed compact set. The disk isolates the complete principal part at a shared pole. -/
private theorem sLocalStripPoles_mellin_circle_decay_of_polynomialSeparation
    (χ : PontryaginDual Jₛ) (A : ℝ) (hsep : sLocalFinitePolePolynomialSeparation χ)
    (f : Tests) (K : Set Jₛ) (hK : IsCompact K) (N : ℕ) :
    ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| →
      ∃ r ∈ Ioo (0 : ℝ) 1, ∀ g ∈ K,
        (∀ z ∈ Metric.closedBall a.val r, z ≠ a.val →
          AnalyticAt ℂ (fun s ↦ ((((normₛ g).val : ℝ) : ℂ) ^ (-s)) * Z(f,χ,s)) z) ∧
        ∀ z ∈ Metric.sphere a.val r,
          ‖((((normₛ g).val : ℝ) : ℂ) ^ (-z)) * Z(f,χ,z)‖ ≤ C / (1 + |a.val.im|) ^ N := by
  obtain ⟨η, he, heq, _⟩ := sLocal_character_extension χ
  obtain ⟨d, c, hc, H, hgeom⟩ := sLocalStripPoles_polynomial_isolating_circles χ A hsep
  obtain ⟨k, hk, hprod⟩ := reciprocal_euler_product_lower_of_separated χ η he heq
  obtain ⟨D, hD, hkernel⟩ := sLocalNormPower_bounded_on_compact_strip K hK (-1) 1
  let n := Fintype.card S
  let M := N+d*n
  obtain ⟨L, hL, Y, htail⟩ :=
    RiemannMasullo.sLocalIdelicZFunction_cleared_strip_tails χ η f he heq (-1) 1 M
  let B := (2:ℝ)^M*L/(k*c^n)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨D*B, mul_nonneg hD hB, max H (max (Y+1) 3), fun a ha ↦ ?_⟩
  let h := 1 + |a.val.im|
  let r := c/h^d
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨hr, hr₁, har, hreg, hcirc⟩ := hgeom a ((le_max_left _ _).trans_lt ha)
  refine ⟨r, ⟨hr, hr₁⟩, fun g hg ↦ ⟨?_, ?_⟩⟩
  · intro z hz hne
    have hp := sLocalIdelicZFunction_poles f χ z
    rw [min_eq_left (hreg z hz hne)] at hp
    have hzeta := ((sLocalIdelicZFunction_meromorphic f χ)
      (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hp
    have hpos : 0 < ((normₛ g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    exact ((differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hpos.ne'))).analyticAt z).mul hzeta
  · intro z hz
    have hd : ‖z-a.val‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    have hre : |z.re| ≤ r := by
      simpa [Complex.sub_re, har, hd] using Complex.abs_re_le_norm (z-a.val)
    have hzre : z.re ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [(abs_le.mp hre).1], by linarith [(abs_le.mp hre).2]⟩
    have him : |a.val.im| ≤ |z.im|+r := by
      calc
        |a.val.im| = |(a.val-z).im + z.im| := by rw [Complex.sub_im, sub_add_cancel]
        _ ≤ |(a.val-z).im| + |z.im| := abs_add_le _ _
        _ ≤ _ := by linarith [Complex.abs_im_le_norm (a.val-z), norm_sub_rev a.val z]
    have hY : Y + 1 < |a.val.im| := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt ha
    have h3 : 3 < |a.val.im| := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt ha
    have hzbig : Y < |z.im| := by linarith
    have hh₂ : h ≤ 2*|z.im| := by dsimp only [h]; linarith
    have hclear := htail z hzre hzbig
    rw [norm_mul] at hclear
    have hp := hprod z r hr hr₁.le (hcirc z hz)
    have hzbound : ‖Z(f,χ,z)‖*h^N ≤ B := absorb_euler_circle_loss N d n hh (abs_nonneg _) hc hk
      (norm_nonneg _) hh₂ hp hclear
    apply (le_div_iff₀ (pow_pos hh N)).mpr
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hkernel g hg z hzre) hzbound
      (mul_nonneg (norm_nonneg _) (pow_nonneg hh.le _)) hD

/-- Every complete Mellin residue satisfies an arbitrary inverse-power bound in the
ordinate, for each fixed test and uniformly on compact sets of idèles. The radius
factor in the Cauchy estimate is at most one. -/
private theorem sLocalStripPoles_residue_decay_of_polynomialSeparation
    (χ : PontryaginDual Jₛ) (A : ℝ) (hsep : sLocalFinitePolePolynomialSeparation χ)
    (f : Tests) (K : Set Jₛ) (hK : IsCompact K) (N : ℕ) :
    ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ a : strip(χ,A), T < |a.val.im| → ∀ g ∈ K,
      ‖sLocalMellinPoleTerm χ f g a.val‖ ≤ C / (1 + |a.val.im|)^N := by
  obtain ⟨C,hC,T,hh⟩ := sLocalStripPoles_mellin_circle_decay_of_polynomialSeparation χ A hsep f K hK N
  refine ⟨C,hC,T,fun a ha g hg ↦ ?_⟩
  obtain ⟨r,hr,h⟩ := hh a ha
  obtain ⟨hreg,hcirc⟩ := h g hg
  rw [sLocalMellinPoleTerm, norm_mul, norm_star, Circle.norm_coe, one_mul]
  exact (norm_complexResidue_le_circle hr.1 hreg hcirc).trans
    (mul_le_of_le_one_left (by positivity) hr.2.le)

/-- A varying circle of radius less than one transfers its height bound to every principal
Laurent coefficient simultaneously, with the same constant and height cutoff. -/
private theorem sLocalZLaurentCoeff_neg_decay_of_circle_decay (χ : PontryaginDual Jₛ) (A : ℝ)
    (f : Tests) (N : ℕ) {C T : ℝ} (hC : 0 ≤ C)
    (hcircle : ∀ a : strip(χ,A), T < |a.val.im| → ∃ r ∈ Ioo (0 : ℝ) 1,
      (∀ z ∈ Metric.closedBall a.val r, z ≠ a.val → AnalyticAt ℂ (fun s ↦ Z(f,χ,s)) z) ∧
      ∀ z ∈ Metric.sphere a.val r, ‖Z(f,χ,z)‖ ≤ C / (1 + |a.val.im|)^N) :
    ∀ a : strip(χ,A), T < |a.val.im| → ∀ k : ℕ, 0 < k →
      ‖sLocalZLaurentCoeff f (chart(χ) a.val) (-(k : ℤ))‖ ≤ C / (1 + |a.val.im|)^N := by
  intro a ha k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨r, hr, hZ, hb⟩ := hcircle a ha
  have hM : 0 ≤ C / (1 + |a.val.im|)^N := by positivity
  rw [sLocalZLaurentCoeff_neg_succ_eq_residue]
  refine (norm_complexResidue_le_circle (C := C / (1 + |a.val.im|)^N) hr.1 ?_ ?_).trans
    (mul_le_of_le_one_left hM hr.2.le)
  · intro z hz hne
    exact ((analyticAt_id.sub analyticAt_const).pow j).mul (hZ z hz hne)
  · intro z hz
    have hd : ‖z - a.val‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    rw [norm_mul, norm_pow, hd]
    exact (mul_le_mul_of_nonneg_left (hb z hz) (pow_nonneg hr.1.le j)).trans
      (mul_le_of_le_one_left hM (pow_le_one₀ hr.1.le hr.2.le))

/-- A height bound on the circles for each test gives a single bound, at every pole and every
principal order, for any bounded set of Schwartz–Bruhat tests. -/
private theorem sLocalZLaurentCoeff_neg_bound_on_bounded_of_circle_decay (χ : PontryaginDual Jₛ)
    (A : ℝ) (N : ℕ) (hcircle : ∀ f : Tests, ∃ C ≥ (0 : ℝ), ∃ T : ℝ,
      ∀ a : strip(χ,A), T < |a.val.im| → ∃ r ∈ Ioo (0 : ℝ) 1,
        (∀ z ∈ Metric.closedBall a.val r, z ≠ a.val → AnalyticAt ℂ (fun s ↦ Z(f,χ,s)) z) ∧
        ∀ z ∈ Metric.sphere a.val r, ‖Z(f,χ,z)‖ ≤ C / (1 + |a.val.im|)^N)
    (B : Set Tests) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C ≥ (0 : ℝ), ∀ a : strip(χ,A), ∀ k : ℕ, 0 < k → ∀ f ∈ B,
      ‖sLocalZLaurentCoeff f (chart(χ) a.val) (-(k : ℤ))‖ ≤ C / (1 + |a.val.im|)^N := by
  classical
  let : BarrelledSpace ℂ Tests := (sAdeleSchwartz_montel (F := F) S).1
  let I := strip(χ,A) × {k : ℕ // 0 < k}
  let w (i : I) : ℝ := (1 + |i.1.val.im|)^N
  have hw (i : I) : 0 < w i := by dsimp only [w]; positivity
  let L (i : I) : StrongDual ℂ Tests :=
    (w i : ℂ) • sLocalPrincipalPartCoeff (chart(χ) i.1.val) i.2.val
  have hnorm (i : I) (f : Tests) :
      ‖L i f‖ = w i * ‖sLocalZLaurentCoeff f (chart(χ) i.1.val) (-(i.2.val : ℤ))‖ := by
    simp only [L, smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw i),
      sLocalPrincipalPartCoeff_apply]
  have hpoint (f : Tests) : ∃ M : ℝ, ∀ i : I, ‖L i f‖ ≤ M := by
    obtain ⟨C, hC, T, hc⟩ := hcircle f
    have htail := sLocalZLaurentCoeff_neg_decay_of_circle_decay χ A f N hC hc
    have hlow : {a : strip(χ,A) | ¬ T < |a.val.im|}.Finite :=
      eventually_cofinite.mp (eventually_sLocalStripPoles_abs_im_gt χ A T)
    have hsite (a : strip(χ,A)) : ∃ D : ℝ, ∀ k : ℕ,
        ‖sLocalZLaurentCoeff f (chart(χ) a.val) (-(k : ℤ))‖ ≤ D := by
      obtain ⟨m, _, _, hz, _⟩ := sLocalZLaurentCoeff_hasLaurentSeries f (chart(χ) a.val)
      obtain ⟨D, hD⟩ := ((Finset.range ((-m).toNat + 1)).finite_toSet.image (fun k : ℕ ↦
        ‖sLocalZLaurentCoeff f (chart(χ) a.val) (-(k : ℤ))‖)).bddAbove
      refine ⟨max D 0, fun k ↦ ?_⟩
      by_cases hk : k < (-m).toNat + 1
      · exact (hD ⟨k, Finset.mem_range.mpr hk, rfl⟩).trans (le_max_left _ _)
      · rw [hz _ (by omega), norm_zero]
        exact le_max_right _ _
    choose D hD using hsite
    obtain ⟨Q, hQ⟩ := (hlow.image (fun a : strip(χ,A) ↦ D a * (1 + |a.val.im|)^N)).bddAbove
    refine ⟨max C Q, fun i ↦ ?_⟩
    rw [hnorm, mul_comm]
    by_cases ht : T < |i.1.val.im|
    · exact ((le_div_iff₀ (hw i)).mp (htail i.1 ht i.2 i.2.property)).trans (le_max_left _ _)
    · exact (mul_le_mul_of_nonneg_right (hD i.1 i.2.val) (hw i).le).trans
        ((hQ ⟨i.1, ht, rfl⟩).trans (le_max_right _ _))
  obtain ⟨C, hC⟩ := strongDual_family_bounded_on_bounded_set L hpoint hB
  refine ⟨max C 0, le_max_right _ _, fun a k hk f hf ↦ ?_⟩
  let i : I := ⟨a, ⟨k, hk⟩⟩
  apply (le_div_iff₀ (hw i)).mpr
  rw [mul_comm]
  exact (hnorm i f ▸ hC i f hf).trans (le_max_left _ _)

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323; (8.4.0.2), p. 389. The actual Mellin
residues are absolutely summable for polynomially separated pole centers. For any
assignment the complex sums and their norm sums converge uniformly over each product
of a bounded set of tests and a compact set of idèles. -/
theorem sLocalMellinPoleTerm_separatePlace_absolute_of_polynomialSeparation {ι : Type*}
    (χ : PontryaginDual Jₛ) (A : ℝ) (hsep : sLocalFinitePolePolynomialSeparation χ)
    (assign : ℂ → ι) :
    (∀ f g, Summable (fun a : strip(χ,A) ↦ ‖sLocalMellinPoleTerm χ f g a.val‖)) ∧
    ∀ (v : ι) (B : Set Tests), Bornology.IsVonNBounded ℂ B → ∀ K : Set Jₛ, IsCompact K →
      TendstoUniformlyOn (fun h fg ↦ ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v),
        sLocalMellinPoleTerm χ fg.1 fg.2 a)
        (fun fg ↦ sLocalAssignedMellinPoleSum χ A assign v fg.1 fg.2) (atBot ×ˢ atTop) (B ×ˢ K) ∧
      TendstoUniformlyOn (fun h fg ↦ ∑ a ∈ (sLocalStripPoleWindow χ A h).filter (assign · = v),
        ‖sLocalMellinPoleTerm χ fg.1 fg.2 a‖)
        (fun fg ↦ ∑' a : strip(χ,A),
          if assign a.val = v then ‖sLocalMellinPoleTerm χ fg.1 fg.2 a.val‖ else 0)
        (atBot ×ˢ atTop) (B ×ˢ K) :=
  sLocalMellinPoleTerm_separatePlace_absolute_of_residue_decay χ A
    (fun f K hK ↦ sLocalStripPoles_residue_decay_of_polynomialSeparation χ A hsep f K hK 2) assign

/-- Paper: Theorem 7.1.2.3, pp. 317–323. On a pole-free left line, inverse-polynomial
separation of distinct finite pole centers implies the full separate-place expansion
for every assignment. Both uniform convergence clauses and the bounded-test remainder
refer to the genuine S-local theta function and its Mellin transform.
Deviation: Each shared pole contributes its complete principal part once. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_polynomialSeparation
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A) (hsep : sLocalFinitePolePolynomialSeparation χ)
    (hLeft : ∀ a : ℂ, a.re = -A → 0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a)
    (assign : ℂ → Places) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign :=
  sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_of_residue_decay χ A hA
    (fun f K hK ↦ sLocalStripPoles_residue_decay_of_polynomialSeparation χ A hsep f K hK 2) hLeft assign

/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323, and (8.4.0.2), p. 389. For a bounded
set of tests, one summable function on the distinct strip poles dominates every negative
Laurent coefficient, uniformly in its order and in the test.
Deviation: The hypothesis allows coincident finite poles but bounds the approach of
distinct centers. All negative coefficients come from the actual Mellin chart. -/
theorem sLocalZLaurentCoeff_neg_summable_majorant_of_polynomialSeparation
    (χ : PontryaginDual Jₛ) (A : ℝ) (hsep : sLocalFinitePolePolynomialSeparation χ)
    (B : Set Tests) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ W : strip(χ,A) → ℝ, Summable W ∧ ∀ a : strip(χ,A), ∀ k : ℕ, 0 < k → ∀ f ∈ B,
      ‖sLocalZLaurentCoeff f (chart(χ) a.val) (-(k : ℤ))‖ ≤ W a := by
  obtain ⟨C, _, h⟩ := sLocalZLaurentCoeff_neg_bound_on_bounded_of_circle_decay χ A 2
    (fun f ↦ by
      obtain ⟨D, hD, T, hT⟩ :=
        sLocalStripPoles_mellin_circle_decay_of_polynomialSeparation χ A hsep f {1} isCompact_singleton 2
      refine ⟨D, hD, T, fun a ha ↦ ?_⟩
      obtain ⟨r, hr, hb⟩ := hT a ha
      exact ⟨r, hr, by simpa using hb 1 (mem_singleton _)⟩) B hB
  refine ⟨fun a ↦ C / (1 + |a.val.im|)^2, ?_, h⟩
  simpa [div_eq_mul_inv] using (summable_sLocalStripPoles_inv_height_sq_all χ A).mul_left C

end

end RiemannMasullo.Isolated
